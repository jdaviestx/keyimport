import java.io.InputStream;
import java.io.OutputStream;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.Arrays;
import java.math.BigInteger;
import java.security.KeyStore;
import java.security.KeyStoreException;
import java.security.Key;
import java.security.KeyFactory;
import java.security.PrivateKey;
import java.security.NoSuchAlgorithmException;
import java.security.spec.KeySpec;
import java.security.spec.PKCS8EncodedKeySpec;
import java.security.spec.RSAPrivateCrtKeySpec;
import java.security.spec.InvalidKeySpecException;
import java.security.cert.Certificate;
import java.security.cert.X509Certificate;
import java.security.cert.CertificateFactory;
import java.security.cert.CertificateException;

/**
 * Import an existing key into a keystore.  This creates a key entry as though you had
 * submitted a "genkey" request so that a subsequent "import" command will import the
 * certificate correctly.
 */
public class KeyImport	{
	private static final int invCodes[] = {
		-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,	// 16
		-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, // 32
		-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 62, -1, -1, -1, 63, // 48
		52, 53, 54, 55, 56, 57, 58, 59, 60, 61, -1, -1, -1, 64, -1, -1, // 64
		-1,  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, // 80
		15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, -1, -1, -1, -1, -1,	// 96
		-1, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, // 112
		41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, -1, -1, -1, -1, -1  // 128
	};

	private static byte[] base64Decode(String input)    {
		if (input.length() % 4 != 0)    {
				throw new IllegalArgumentException("Invalid base64 input");
		}
		byte decoded[] = new byte[((input.length() * 3) / 4) - 
			(input.indexOf('=') > 0 ? (input.length() - input.indexOf('=')) : 0)];
		char[] inChars = input.toCharArray();
		int j = 0;
		int b[] = new int[4];
		for (int i = 0; i < inChars.length; i += 4)     {
			b[0] = invCodes[inChars[i]];
			b[1] = invCodes[inChars[i + 1]];
			b[2] = invCodes[inChars[i + 2]];
			b[3] = invCodes[inChars[i + 3]];
			decoded[j++] = (byte) ((b[0] << 2) | (b[1] >> 4));
			if (b[2] < 64)      {
				decoded[j++] = (byte) ((b[1] << 4) | (b[2] >> 2));
				if (b[3] < 64)  {
					decoded[j++] = (byte) ((b[2] << 6) | b[3]);
				}
			}
		}

		return decoded;
	}

	private static String toHex(byte b)	{
		String hex = "";

		if ((b & 0xF0) > 0x90)	{
			hex += (char) ('A' + (((b & 0xF0) >> 4) - 10));
		} else	{
			hex += (char) ('0' + ((b & 0xF0) >> 4));
		}

		if ((b & 0x0F) > 0x09)	{
			hex += (char) ('A' + ((b & 0x0F) - 10));
		} else	{
			hex += (char) ('0' + (b & 0x0F));
		}

		return hex;
	}

	/**
	 * Bare-bones ASN.1 parser that can only deal with a structure that contains integers
	 * (as I expect for the RSA private key format given in PKCS #1 and RFC 3447).
	 * @param b the bytes to be parsed as ASN.1 DER
	 * @param integers an output array to which all integers encountered during the parse
	 * 	will be appended in the order they're encountered.  It's up to the caller to determine
	 * 	which is which.
	 */
	private static void ASN1Parse(byte[] b, List<BigInteger> integers)	{
		int pos = 0;
		while (pos < b.length)	{
			byte tag = b[pos++];
			int length = b[pos++];
			if ((length & 0x80) != 0)	{
				byte[] lenlen = new byte[length & 0x7F];
				System.arraycopy(b, pos, lenlen, 0, lenlen.length);
				BigInteger ilen = new BigInteger(1, lenlen);	// force the result to be unsigned
				length = ilen.intValue();
				pos += lenlen.length;
			}
			byte[] contents = new byte[length];
			System.arraycopy(b, pos, contents, 0, length);
			pos += length;

			if (tag == 0x30)	{	// sequence
				ASN1Parse(contents, integers);
			} else if (tag == 0x02)	{	// Integer
				BigInteger i = new BigInteger(contents);
				integers.add(i);
			}
		}
	}

	/**
	 * Read a PKCS #8, Base64-encrypted file as a Key instance.
	 * If the file is encrypted, decrypt it via:
	 * openssl rsa -in keyfilename -out decryptedkeyfilename
	 * TODO deal with an encrypted private key internally
	 */
	private static PrivateKey readPrivateKeyFile(String keyFileName) 
			throws IOException,
						 NoSuchAlgorithmException,
						 InvalidKeySpecException	{
		BufferedReader in = new BufferedReader(new FileReader(keyFileName));
		try	{
			String line;
			boolean readingKey = false;
			boolean pkcs8Format = false;
			boolean rsaFormat = false;
			StringBuffer base64EncodedKey = new StringBuffer();
			while ((line = in.readLine()) != null)	{
				if (readingKey)	{
					if (line.trim().equals("-----END RSA PRIVATE KEY-----"))	{	// PKCS #1
						readingKey = false;
					} else if (line.trim().equals("-----END PRIVATE KEY-----"))	{	// PKCS #8
						readingKey = false;
					} else	{
						base64EncodedKey.append(line.trim());
					}
				} else if	(line.trim().equals("-----BEGIN RSA PRIVATE KEY-----"))	{
					readingKey = true;
					rsaFormat = true;
				} else if	(line.trim().equals("-----BEGIN PRIVATE KEY-----"))	{
					readingKey = true;
					pkcs8Format = true;
				}
			}
			if (base64EncodedKey.length() == 0)	{
				throw new IOException("File '" + keyFileName + 
					"' did not contain an unencrypted private key");
			}

			byte[] bytes = base64Decode(base64EncodedKey.toString());

			// PKCS#1 format

/*
			for (int i = 0; i < bytes.length; i++)	{
				System.out.print(toHex(bytes[i]));
			}
			*/

			// PKCS #8 as in: http://www.agentbob.info/agentbob/79-AB.html
			KeyFactory kf = KeyFactory.getInstance("RSA");
			KeySpec spec = null;
			if (pkcs8Format)	{
				spec = new PKCS8EncodedKeySpec(bytes);
			} else if (rsaFormat)	{
				List<BigInteger> rsaIntegers = new ArrayList<BigInteger>();
				ASN1Parse(bytes, rsaIntegers);
				if (rsaIntegers.size() < 8)	{
					System.err.println("'" + keyFileName + "' does not appear to be a properly formatted " +
						"RSA key");
					System.exit(0);
				}
				BigInteger publicExponent = rsaIntegers.get(2);
				BigInteger privateExponent = rsaIntegers.get(3);
				BigInteger modulus = rsaIntegers.get(1);
				BigInteger primeP = rsaIntegers.get(4);
				BigInteger primeQ = rsaIntegers.get(5);
				BigInteger primeExponentP = rsaIntegers.get(6);
				BigInteger primeExponentQ = rsaIntegers.get(7);
				BigInteger crtCoefficient = rsaIntegers.get(8);
				// If I just use RSAPrivateKeySpec, the SSL connection fails with
				// ERR_SSL_PROTOCOL_ERROR; Tomcat starts up and the import succeeds
				//spec = new RSAPrivateKeySpec(modulus, privateExponent);
				spec = new RSAPrivateCrtKeySpec(modulus, publicExponent, privateExponent,
					primeP, primeQ, primeExponentP, primeExponentQ, crtCoefficient);
			}
			return kf.generatePrivate(spec);
		} finally	{
			in.close();
		}
	}

	static class Parameter	{
		String flag;
		boolean required;
		String description;
		String defaultValue;

		public Parameter(String flag, boolean required, String description, String defaultValue)	{
			this.flag = flag;
			this.required = required;
			this.description = description;
			this.defaultValue = defaultValue;
		}

		public boolean equals(Object o)	{
			return (o instanceof Parameter) && (this.flag.equals(((Parameter) o).flag));
		}
	}

	private static String KEY_FILE = "-keyFile";
	private static String ALIAS = "-alias";
	private static String CERT_FILE = "-certificateFile";
	private static String KEY_STORE = "-keystore";
	private static String KEY_STORE_PASSWORD = "-keystorePassword";
	private static String KEY_STORE_TYPE = "-keystoreType";
	private static String KEY_PASSWORD = "-keyPassword";

	private static List<Parameter> paramDesc = Arrays.asList(
		new Parameter[] {
			new Parameter(KEY_FILE, true, "Name of file containing a private key in PEM or DER form", null),
			new Parameter(ALIAS, true, "The alias that this key should be imported as", null),
			new Parameter(CERT_FILE, true, "Name of file containing the certificate that corresponds to the key named by '-keyFile'", null),
			new Parameter(KEY_STORE, false, "Name of the keystore to import the private key into.", "~/.keystore"),
			new Parameter(KEY_STORE_PASSWORD, false, "Keystore password", "changeit"),
			new Parameter(KEY_STORE_TYPE, false, "Type of keystore; must be JKS or PKCS12", "JKS"),
			// If this password is different than the key store password, Tomcat (at least) chokes on it with: java.security.UnrecoverableKeyException: Cannot recover key
			new Parameter(KEY_PASSWORD, false, "The password to protect the imported key with", "changeit")
		});

	private static void usage()	{
		for (Parameter param : paramDesc)	{
			System.out.println(param.flag + "\t" + (param.required ? "required" : "optional") + "\t" +
				param.description + "\t" + 
				(param.defaultValue != null ? ("default '" + param.defaultValue + "'") : ""));
		}
	}

	public static void main(String[] args) throws IOException, 
																								KeyStoreException,
																								NoSuchAlgorithmException,
																								CertificateException,
																								InvalidKeySpecException	{
		Map<String, String> parsedArgs = new HashMap<String, String>();
		for (Parameter param : paramDesc)	{
			if (param.defaultValue != null)	{
				parsedArgs.put(param.flag, param.defaultValue);
			}
		}
		for (int i = 0; i < args.length; i += 2)	{
			parsedArgs.put(args[i], args[i + 1]);
		}

		boolean invalidParameters = false;
		for (Parameter param : paramDesc)	{
			if (param.required && parsedArgs.get(param.flag) == null)	{
				System.err.println("Missing required parameter " + param.flag);
				invalidParameters = true;
			}
		}
		for (String key : parsedArgs.keySet())	{
			if (!paramDesc.contains(new Parameter(key, false, null, null)))	{
				System.err.println("Invalid parameter '" + key + "'");
				invalidParameters = true;
			}
		}
		if (invalidParameters)	{
			usage();
			System.exit(0);
		}

		KeyStore ks = KeyStore.getInstance(parsedArgs.get(KEY_STORE_TYPE));
		InputStream keyStoreIn = new FileInputStream(parsedArgs.get(KEY_STORE));
		try	{
			ks.load(keyStoreIn, parsedArgs.get(KEY_STORE_PASSWORD).toCharArray());
		} finally	{
			keyStoreIn.close();
		}

		Certificate cert;
		CertificateFactory fact = CertificateFactory.getInstance("X.509");
		FileInputStream certIn = new FileInputStream(parsedArgs.get(CERT_FILE));
		try	{
			cert = fact.generateCertificate(certIn);
		} finally	{
			certIn.close();
		}

		PrivateKey privateKey = readPrivateKeyFile(parsedArgs.get(KEY_FILE));
		ks.setKeyEntry(parsedArgs.get(ALIAS), privateKey, 
			parsedArgs.get(KEY_PASSWORD).toCharArray(), new Certificate[] {cert});

		OutputStream keyStoreOut = new FileOutputStream(parsedArgs.get(KEY_STORE));
		try	{
			ks.store(keyStoreOut, parsedArgs.get(KEY_STORE_PASSWORD).toCharArray());
		} finally	{
			keyStoreOut.close();
		}
	}
}
