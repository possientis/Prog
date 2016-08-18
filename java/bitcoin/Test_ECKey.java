import java.util.Comparator;
import java.util.Date;
import java.util.Arrays;
import java.math.BigInteger;
import java.lang.Math;
import java.security.SecureRandom;
import javax.xml.bind.DatatypeConverter;

import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.DumpedPrivateKey;
import org.bitcoinj.wallet.Protos.Wallet.EncryptionType;
import org.bitcoinj.crypto.LazyECPoint;
import org.bitcoinj.crypto.KeyCrypter;
import org.bitcoinj.crypto.KeyCrypterScrypt;
import org.bitcoinj.crypto.EncryptedData;


import org.spongycastle.crypto.params.ECDomainParameters;
import org.spongycastle.crypto.params.KeyParameter;
import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.crypto.digests.RIPEMD160Digest;

import com.google.common.primitives.UnsignedBytes;


public class Test_ECKey implements Test_Interface {


  public void run(){
    logMessage("ECKey unit test running ...");
    checkNestedClasses();
    checkAgeComparator();
    checkCurve();
    checkHalfCurveOrder();
    checkFakeSignatures();
    checkPubKeyComparator();
    checkConstructorDefault();
    checkConstructorFromSecureRandom();
    checkCompressPoint();
    checkCompressPointLazy();
    checkDecompress();
    checkDecompressPoint();
    checkDecompressPointLazy();
    checkDecrypt();
    checkDecryptFromKeyCrypter();
    checkEncrypt();
    checkEncryptionIsReversible();
    checkECKeyEquals();
    checkFormatKeyWithAddress();
    checkFromASN1();
    checkFromEncrypted();
    checkFromPrivateFromBigInteger();
    checkFromPrivateFromBigIntegerBool();
    checkFromPrivateFromBytes();
    checkFromPrivateFromBytesBool();
    checkFromPrivateAndPrecalculatedPublic();
    checkFromPrivateAndPrecalculatedPublicFromBytes();
    checkFromPublicOnly();
    checkFromPublicOnlyFromBytes();
    checkGetCreationTimeSeconds();
    checkGetEncryptedData();
    checkGetEncryptedPrivateKey();
    checkGetEncryptionType();
    checkGetKeyCrypter();
    checkGetPrivateKeyAsHex();
    checkGetPrivateKeyAsWiF();
    checkGetPrivateKeyEncoded();
    checkGetPrivKey();
    checkGetPrivKeyBytes();
    checkGetPubKey();
    checkGetPubKeyHash();
    checkGetPubKeyPoint();
    checkGetPublicKeyAsHex();
    checkGetSecretBytes();
    checkHashCode();
    checkHasPrivKey();
    checkIsCompressed();
    checkIsEncrypted();
    checkIsPubKeyCanonical();
    checkIsPubKeyOnly();
    checkIsWatching();
    checkMaybeDecrypt();
    checkPublicKeyFromPrivate();
    checkPublicPointFromPrivate();
    checkRecoverFromSignature();
    checkSetCreationTimeSeconds();
    checkSign();
    checkSignFromKeyParameter();
    checkSignedMessageToKey();
    checkSignMessage();
    checkSignMessageFromKeyParameter();
    checkToAddress();
    checkToASN1();
    checkToString();
    checkToStringWithPrivate();
    checkVerify();
    checkVerifyFromPubKeySigAsBytes();
    checkVerifyFromPubKey();
    checkVerifyHash();
    checkVerifyMessage();
    checkVerifyOrThrow();
    checkVerifyOrThrowSigAsBytes();

  }

  private String getFieldPrimeAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
  }

  private BigInteger getFieldPrime(){
    return new BigInteger(getFieldPrimeAsHex(), 16);
  }

  private String getCurveOrderAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"; 
  }

  private BigInteger getCurveOrder(){
    return new BigInteger(getCurveOrderAsHex(), 16);
  }

  private String getCurveGeneratorXAsHex(){
    return "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"; 
  }

  private BigInteger getCurveGeneratorX(){
    return new BigInteger(getCurveGeneratorXAsHex(), 16);
  }

  private String getCurveGeneratorYAsHex(){
    return "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";
  }

  // used to initialize private field
  private BigInteger getCurveGeneratorY(){
    return new BigInteger(getCurveGeneratorYAsHex(), 16);
  }

  // private key example from 'Mastering bitcoin'
  private String getSecret1AsHex(){
    return "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";
  }
    
  private BigInteger getSecret1(){
    return new BigInteger(getSecret1AsHex(), 16);
  }

  private String getSecret1AsWiF(){
    // 0x80 | private key | 0x01 | checksum
    // This is main net so version byte is 0x80 = 128
    // This is a compressed key of single byte suffix 0x01 added
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j 1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD 
    return "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ";
    //      KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ
  }

  private String getSecret1AsWiFUncomp(){
    // 0x80 | private key | checksum
    // This is main net so version byte is 0x80 = 128
    // This is an uncompressed key so no single 0x01 suffix byte
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j 1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD 
    return "5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn";
    //      5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn
  }


  private String getSecret1AsWiFTest(){
    // 0xEF | private key | 0x01 | checksum
    // This is a test network so version byte is 0xEF = 239
    // This is a compressed key so single byte suffix 0x01 added
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j -n XTN 1E99423A4ED27608A15A2616A2B0E9E52CED33...C8FFC6A526AEDD 
    return "cNcBUemoNGVRN9fRtxrmtteAPQeWZ399d2REmX1TBjvWpRfNMy91";
    //      cNcBUemoNGVRN9fRtxrmtteAPQeWZ399d2REmX1TBjvWpRfNMy91
  }

  private String getSecret1AsWiFTestUncomp(){
    // 0xEF | private key | checksum
    // This is a test network so version byte is 0xEF = 239
    // This is an uncompressed key so no single 0x01 suffix byte
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j -n XTN 1E99423A4ED27608A15A2616A2B0E9E52CED33...C8FFC6A526AEDD 
    return "91pPmKypfMGxN73N3iCjLuwBjgo7F4CpGQtFuE9FziSieVTY4jn";
    //      91pPmKypfMGxN73N3iCjLuwBjgo7F4CpGQtFuE9FziSieVTY4jn
  }


  private byte[] getSecret1AsBytes(){
    /*
    return "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";
    */
    byte [] bytes = { (byte) 0x1E, (byte) 0x99, (byte) 0x42, (byte) 0x3A,
                      (byte) 0x4E, (byte) 0xD2, (byte) 0x76, (byte) 0x08,
                      (byte) 0xA1, (byte) 0x5A, (byte) 0x26, (byte) 0x16,
                      (byte) 0xA2, (byte) 0xB0, (byte) 0xE9, (byte) 0xE5,
                      (byte) 0x2C, (byte) 0xED, (byte) 0x33, (byte) 0x0A,
                      (byte) 0xC5, (byte) 0x30, (byte) 0xED, (byte) 0xCC,
                      (byte) 0x32, (byte) 0xC8, (byte) 0xFF, (byte) 0xC6,
                      (byte) 0xA5, (byte) 0x26, (byte) 0xAE, (byte) 0xDD}; 
    return bytes;
  }

  // obtained from independent source
  private String getSecret1PubKeyXAsHex(){
    return "F028892BAD7ED57D2FB57BF33081D5CFCF6F9ED3D3D7F159C2E2FFF579DC341A";
  }

  private BigInteger getSecret1PubKeyX(){
    return new BigInteger(getSecret1PubKeyXAsHex(), 16);
  }


  // obtained from independent source
  private String getSecret1PubKeyYAsHex(){
    // leading zero matters here, as we append strings together
    return "07CF33DA18BD734C600B96A72BBC4749D5141C90EC8AC328AE52DDFE2E505BDB";
  }


  private BigInteger getSecret1PubKeyY(){
    return new BigInteger(getSecret1PubKeyYAsHex(), 16);
  }

  private String getSecret1PubKeyAsHex(){
    return "03" + getSecret1PubKeyXAsHex();
  }

  private BigInteger getSecret1PubKey(){
    return new BigInteger(getSecret1PubKeyAsHex(), 16);
  }

  private String getSecret1PubKeyUncompAsHex(){
    return "04" + getSecret1PubKeyXAsHex() + getSecret1PubKeyYAsHex();
  }


  private BigInteger getSecret1PubKeyUncomp(){
    return new BigInteger(getSecret1PubKeyUncompAsHex(), 16);
  }

  private String getSecret1PubKeyHashAsHex(){
    return "BBC1E42A39D05A4CC61752D6963B7F69D09BB27B";
  }

  private BigInteger getSecret1PubKeyHash(){
    return new BigInteger(getSecret1PubKeyHashAsHex(), 16);
  }


  private String getSecret1PubKeyHashUncompAsHex(){
    return "211B74CA4686F81EFDA5641767FC84EF16DAFE0B";
  }

  private BigInteger getSecret1PubKeyHashUncomp(){
    return new BigInteger(getSecret1PubKeyHashUncompAsHex(), 16);
  }

  private String getSecret1Address(){
    return "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy";
  }

  private String getSecret1AddressUncomp(){
    return "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x";
  }

  private  NetworkParameters getMainNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_MAINNET);
  }

  private  NetworkParameters getRegTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_REGTEST);
  }

  private  NetworkParameters getTestNetNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_TESTNET);
  }

  private  NetworkParameters getUnitTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_UNITTESTNET);
  }
  // data derived from independent sources
  private final BigInteger fieldPrime = getFieldPrime();
  private final BigInteger curveOrder = getCurveOrder();
  private final BigInteger halfCurveOrder = curveOrder.shiftRight(1); // div 2
  private final BigInteger curveGeneratorX = getCurveGeneratorX();
  private final BigInteger curveGeneratorY = getCurveGeneratorY();
  private final String curveOrderAsHex = getCurveOrderAsHex();


  // key from Mastering Bitcoin
  private final BigInteger secret1 = getSecret1();
  private final BigInteger secret1PubKeyX = getSecret1PubKeyX();
  private final BigInteger secret1PubKeyY = getSecret1PubKeyY();
  private final BigInteger secret1PubKey = getSecret1PubKey();
  private final BigInteger secret1PubKeyUncomp = getSecret1PubKeyUncomp();
  private final BigInteger secret1PubKeyHash = getSecret1PubKeyHash();
  private final BigInteger secret1PubKeyHashUncomp = getSecret1PubKeyHashUncomp();
  
  private final String secret1AsHex = getSecret1AsHex();
  private final String secret1AsWiF = getSecret1AsWiF();
  private final String secret1AsWiFUncomp = getSecret1AsWiFUncomp();
  private final String secret1AsWiFTest = getSecret1AsWiFTest();
  private final String secret1AsWiFTestUncomp = getSecret1AsWiFTestUncomp();
  private final String secret1PubKeyXAsHex = getSecret1PubKeyXAsHex();
  private final String secret1PubKeyYAsHex = getSecret1PubKeyYAsHex();
  private final String secret1PubKeyAsHex = getSecret1PubKeyAsHex();
  private final String secret1PubKeyUncompAsHex = getSecret1PubKeyUncompAsHex();
  private final String secret1Address = getSecret1Address();
  private final String secret1AddressUncomp = getSecret1AddressUncomp();

  private final byte[] secret1AsBytes = getSecret1AsBytes();

  private final ECKey key1 = ECKey.fromPrivate(secret1);
  private final ECKey key1Uncomp = ECKey.fromPrivate(secret1, false);

  // other data
  private final NetworkParameters mainNet = getMainNetwork();
  private final NetworkParameters regTestNet = getRegTestNetwork();
  private final NetworkParameters testNetNet = getTestNetNetwork();
  private final NetworkParameters unitTestNet = getUnitTestNetwork();
  private final SecureRandom random = new SecureRandom();

  private BigInteger getRandomSecret(){
    byte bytes[] = new byte[32];
    boolean isGood = false;
    BigInteger secret = BigInteger.ZERO;

    while(!isGood){
      random.nextBytes(bytes);
      secret = new BigInteger(1, bytes);  // unsigned
      // we want secret to satisfy 1 < secret < curveOrder
      if(secret.compareTo(BigInteger.ONE) > 0 && secret.compareTo(curveOrder) < 0){
        isGood = true;
      }
    }

    return secret;
  }

  private boolean isKeyFromSecret1(ECKey key){
    if (!key.getPrivKey().equals(secret1)) return false;
    return true;
  }

  private BigInteger sqrt(BigInteger n, boolean isEven){
    // Let p be the underlying prime.
    // This function returns the square root of n modulo p with given parity
    // Since p = 3 mod 4, whenever n is a quadratic residue modulo p, a 
    // square root of n is n^[(p+1)/4] mod p. This follows from Euler' criterion.
    // Note that p = 3 mod 4 ensures that (p+1)/4 in indeed an integer.
    BigInteger p = fieldPrime;
    BigInteger two = BigInteger.ONE.shiftLeft(1);
    BigInteger exp = p.add(BigInteger.ONE).shiftRight(2); // (p+1)/4
    BigInteger arg = n.mod(p);
    BigInteger n1 = arg.modPow(exp, p); // first square root
    BigInteger n2 = n1.negate().mod(p); // second square root

    // checking n1 and n2 are indeed square roots modulo p
    checkEquals(n1.multiply(n1).mod(p), arg, "sqrt.1");
    checkEquals(n2.multiply(n2).mod(p), arg, "sqrt.2");

    // retrieving parity of each square root
    boolean isEven1 = (n1.mod(two) == BigInteger.ZERO);
    boolean isEven2 = (n2.mod(two) == BigInteger.ZERO);

    // if one is even, the other should be odd
    checkCondition((isEven1 && !isEven2) || (!isEven1 && isEven2), "sqrt.3");

    return isEven ? (isEven1 ? n1 : n2) : (isEven1 ? n2 : n1);
  }

  private BigInteger YFromX(BigInteger x, boolean isEven){
    // returns Y such that Y^2 = X^3 + 7 modulo p of given parity
    BigInteger p = fieldPrime;
    BigInteger seven = BigInteger.valueOf(7);
    BigInteger square = x.multiply(x).mod(p);
    BigInteger cube = square.multiply(x).mod(p);
    BigInteger sum = cube.add(seven);
    return sqrt(sum, isEven);
  }

  private boolean _isEven(BigInteger y){
    BigInteger p = fieldPrime;
    BigInteger two = BigInteger.ONE.shiftLeft(1);
    BigInteger arg = y.mod(p);
    return (arg.mod(two) == BigInteger.ZERO);
  }
  
  private String _toString(ECKey key){
    StringBuilder builder = new StringBuilder("ECKey{pub HEX="); 
    builder.append(key.getPublicKeyAsHex());
    builder.append(", isEncrypted=");
    builder.append(key.isEncrypted());
    builder.append(", isPubKeyOnly=");
    builder.append(key.isPubKeyOnly());
    builder.append("}");
    return builder.toString();
  }
  
  private String _toStringWithPrivate(ECKey key, NetworkParameters params){
    StringBuilder builder = new StringBuilder("ECKey{pub HEX="); 
    builder.append(key.getPublicKeyAsHex());
    builder.append(", priv HEX=");
    builder.append(key.getPrivateKeyAsHex());
    builder.append(", priv WIF=");
    builder.append(key.getPrivateKeyAsWiF(params));
    builder.append(", isEncrypted=");
    builder.append(key.isEncrypted());
    builder.append(", isPubKeyOnly=");
    builder.append(key.isPubKeyOnly());
    builder.append("}");

    return builder.toString();
  }

  private String _formatKey(ECKey key, boolean priv, NetworkParameters params){
    StringBuilder builder = new StringBuilder("  addr:");
    builder.append(key.toAddress(params));
    builder.append("  hash160:");
    String hash = DatatypeConverter.
                  printHexBinary(key.getPubKeyHash()).
                  toLowerCase();
    builder.append(hash);
    builder.append("  creationTimeSeconds:");
    builder.append(Long.valueOf(key.getCreationTimeSeconds()).toString());

    if(priv){
      builder.append("\n  ");
      builder.append(key.toStringWithPrivate(params));
    }

    builder.append('\n');

    return builder.toString();
  }


  private byte[] _ripemd160(byte[] input){
    // we are not supposed to call this on inputs other
    // than 32 bytes long. Hence this restriction for safety
    checkEquals(32, input.length, "_ripemd160.1");
    byte[] out = new byte[20];
    RIPEMD160Digest digest = new RIPEMD160Digest();
    digest.update(input, 0, input.length);  
    digest.doFinal(out, 0);
    return out;
  }

  // compile time checks
  public void checkNestedClasses(){
    ECKey.ECDSASignature sig;
    ECKey.KeyIsEncryptedException e1;
    ECKey.MissingPrivateKeyException e2;
  }

  // checking static field AGE_COMPARATOR
  public void checkAgeComparator(){
    Comparator<ECKey> comp = ECKey.AGE_COMPARATOR;

    ECKey k1 = new ECKey();
    ECKey k2 = new ECKey();
    // making sure k2 is younger than k1
    k2.setCreationTimeSeconds(10 + k2.getCreationTimeSeconds());

    checkCondition(comp.compare(k1,k1) == 0, "checkAgeComparator.1");
    checkCondition(comp.compare(k2,k2) == 0, "checkAgeComparator.2");
    checkCondition(comp.compare(k1,k2) < 0, "checkAgeComparator.3");
    checkCondition(comp.compare(k2,k1) > 0, "checkAgeComparator.4");
  }

  // checking static field CURVE
  public void checkCurve(){
    ECDomainParameters curve = ECKey.CURVE;
    // checking field prime
    BigInteger prime = curve.getCurve().getField().getCharacteristic();
    checkEquals(prime, fieldPrime, "checkCurve.1");
    // getN() method returns order of elliptic curve
    checkEquals(curve.getN(), curveOrder, "checkCurve.2");
    // getH() method returns the 'cofactor' of elliptic curve (should be 1)
    checkEquals(curve.getH(), BigInteger.ONE, "checkCurve.3");
    // getG() method returns the curve generator
    ECPoint generator = curve.getG();
    checkCondition(generator.isNormalized(), "checkCurve.4");
    BigInteger x = generator.getAffineXCoord().toBigInteger();
    BigInteger y = generator.getAffineYCoord().toBigInteger();
    checkEquals(x, curveGeneratorX, "checkCurve.5");
    checkEquals(y, curveGeneratorY, "checkCurve.6");
    BigInteger a = curve.getCurve().getA().toBigInteger();
    BigInteger b = curve.getCurve().getB().toBigInteger();
    // Y^2 = X^3 + 7 , so a = 0 and b = 7
    checkEquals(a, BigInteger.ZERO, "checkCurve.7");
    checkEquals(b, BigInteger.valueOf(7), "checkCurve.8");
  }

  // checking static field HALF_CURVE_ORDER
  public void checkHalfCurveOrder(){
    BigInteger half = ECKey.HALF_CURVE_ORDER;
    checkEquals(half, halfCurveOrder, "checkHalfCurveOrder.1");
  }

  // checking static fiels FAKE_SIGNATURES
  public void checkFakeSignatures(){
    boolean flag = ECKey.FAKE_SIGNATURES;
    checkEquals(flag, false, "checkFakeSignatures.1");
  }

  // checking static field PUBKEY_COMPARATOR
  public void checkPubKeyComparator(){
    Comparator<ECKey> comp1 = ECKey.PUBKEY_COMPARATOR;
    Comparator<byte[]> comp2 = UnsignedBytes.lexicographicalComparator();
    ECKey key1 = new ECKey();
    ECKey key2 = new ECKey();
    checkEquals(
        comp1.compare(key1,key2),
        comp2.compare(key1.getPubKey(), key2.getPubKey()),
        "checkPubKeyComparator.1"
    );
  }

  public void checkConstructorDefault(){
    ECKey key = new ECKey();  // generate new keypair
    checkNotNull(key, "checkConstructorDefault.1");
    checkCondition(!key.isEncrypted(), "checkConstructorDefault.2");
    checkCondition(key.hasPrivKey(), "checkConstructorDefault.3");
    checkCondition(key.isCompressed(), "checkConstructorDefault.4");
    checkCondition(!key.isPubKeyOnly(), "checkConstructorDefault.5");
    checkCondition(!key.isWatching(), "checkConstructorDefault.6");

  }

  public void checkConstructorFromSecureRandom(){
    ECKey key = new ECKey(random);
    checkNotNull(key, "checkConstructorFromSecureRandom.1");
    checkCondition(!key.isEncrypted(), "checkConstructorFromSecureRandom.2");
    checkCondition(key.hasPrivKey(), "checkConstructorFromSecureRandom.3");
    checkCondition(key.isCompressed(), "checkConstructorFromSecureRandom.4");
    checkCondition(!key.isPubKeyOnly(), "checkConstructorFromSecureRandom.5");
    checkCondition(!key.isWatching(), "checkConstructorFromSecureRandom.6");
  }

  public void checkCompressPoint(){
    // per point compressed property will be removed soon
    ECKey key = new ECKey();
    ECPoint point1 = key.getPubKeyPoint();
    BigInteger x = point1.getAffineXCoord().toBigInteger();
    BigInteger y = point1.getAffineYCoord().toBigInteger();
    ECPoint point2 = ECKey.CURVE.getCurve().createPoint(x,y);
    ECPoint point3 = ECKey.compressPoint(point2);
    checkEquals(point2, point3, "checkCompressPoint.1");
  }

  public void checkCompressPointLazy(){
    // per point compressed property will be removed soon
    ECKey key = new ECKey();
    ECPoint point1 = key.getPubKeyPoint();
    BigInteger x = point1.getAffineXCoord().toBigInteger();
    BigInteger y = point1.getAffineYCoord().toBigInteger();
    ECPoint point2 = ECKey.CURVE.getCurve().createPoint(x,y);
    LazyECPoint lazy1 = new LazyECPoint(point2);
    LazyECPoint lazy2 = ECKey.compressPoint(lazy1);
    checkCondition(lazy1.equals(lazy2), "checkCompressPointLazy.1");
  }

  public void checkDecompress(){
    // per point compressed property will be removed soon
    ECKey key1 = new ECKey();
    checkCondition(key1.isCompressed(),"checkDecompress.1");
    ECKey key2 = key1.decompress();
    checkCondition(!key2.isCompressed(),"checkDecompress.2");
    checkEquals(key1.getPrivKey(), key2.getPrivKey(), "checkDecompress.3");
  }
  
  public void checkDecompressPoint(){
    // per point compressed property will be removed soon
    ECKey key = new ECKey();
    ECPoint point1 = key.getPubKeyPoint();
    BigInteger x = point1.getAffineXCoord().toBigInteger();
    BigInteger y = point1.getAffineYCoord().toBigInteger();
    ECPoint point2 = ECKey.CURVE.getCurve().createPoint(x,y);
    ECPoint point3 = ECKey.decompressPoint(point2);
    checkEquals(point2, point3, "checkDecompressPoint.1");
  }

  public void checkDecompressPointLazy(){
    // per point compressed property will be removed soon
    ECKey key = new ECKey();
    ECPoint point1 = key.getPubKeyPoint();
    BigInteger x = point1.getAffineXCoord().toBigInteger();
    BigInteger y = point1.getAffineYCoord().toBigInteger();
    ECPoint point2 = ECKey.CURVE.getCurve().createPoint(x,y);
    LazyECPoint lazy1 = new LazyECPoint(point2);
    LazyECPoint lazy2 = ECKey.decompressPoint(lazy1);
    checkCondition(lazy1.equals(lazy2), "checkDecompressPointLazy.1");
  }

  public void checkDecrypt(){
    KeyCrypter crypter1 = new KeyCrypterScrypt();
    KeyParameter aesKey1 = crypter1.deriveKey("some random passphrase");
    ECKey key1 = new ECKey();
    ECKey key2 = key1.encrypt(crypter1, aesKey1); 
    // so we have an encrypted key2
    KeyCrypter crypter2 = key2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some random passphrase"); 
    ECKey key3 = key2.decrypt(aesKey2);
    checkEquals(key1.getPrivKey(), key3.getPrivKey(), "checkDecrypt.1");
  }

  public void checkDecryptFromKeyCrypter(){
    KeyCrypter crypter1 = new KeyCrypterScrypt();
    KeyParameter aesKey1 = crypter1.deriveKey("some random passphrase");
    ECKey key1 = new ECKey();
    ECKey key2 = key1.encrypt(crypter1, aesKey1); 
    // so we have an encrypted key2
    KeyCrypter crypter2 = key2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some random passphrase"); 
    ECKey key3 = key2.decrypt(crypter2, aesKey2);
    checkEquals(
        key1.getPrivKey(), 
        key3.getPrivKey(), 
        "checkDecryptFromKeyCrypter.1"
    );
  }

  public void checkEncrypt(){
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey key1 = new ECKey();
    ECKey key2 = key1.encrypt(crypter, aesKey); 
    checkCondition(key2.isEncrypted(),"checkEncrypt.1");
    checkCondition(key2.isPubKeyOnly(),"checkEncrypt.2");
    checkCondition(!key2.isWatching(),"checkEncrypt.3");
    BigInteger n1 = new BigInteger(1, key1.getPubKey()); 
    BigInteger n2 = new BigInteger(1, key2.getPubKey()); 
    // unencrypted and encrypted key should have the same public key
    checkEquals(n1, n2, "checkEncrypt.4");
  }

  public void checkEncryptionIsReversible(){
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey key1 = new ECKey();
    ECKey key2 = key1.encrypt(crypter, aesKey); 
    checkCondition(
        ECKey.encryptionIsReversible(key1, key2, crypter, aesKey),
        "checkEncryptionIsReversible.1"
    );
    /* this create warning in the log, dunno how to suppress it
    KeyParameter aesWrongKey = crypter.deriveKey("This passphrase is wrong");
    checkCondition(
        !ECKey.encryptionIsReversible(key1, key2, crypter, aesWrongKey),
        "checkEncryptionIsReversible.2"
    );
    */
  }

  public void checkECKeyEquals(){
    ECKey key1 = new ECKey();
    ECKey key2 = new ECKey();
    checkCondition(key1.equals(key1),"checkECKeyEquals.1");
    checkCondition(key2.equals(key2),"checkECKeyEquals.2");
    checkCondition(!key1.equals(key2),"checkECKeyEquals.3");
    checkCondition(!key2.equals(key1),"checkECKeyEquals.3");
  }

  public void checkFormatKeyWithAddress(){
    ECKey key = new ECKey();
    StringBuilder builder = new StringBuilder();
    key.formatKeyWithAddress(false, builder, mainNet);
    String s1 = builder.toString();
    String s2 = _formatKey(key, false, mainNet);
    checkEquals(s1,s2, "checkFormatKeyWithAddress.1");
    builder = new StringBuilder();
    key.formatKeyWithAddress(true, builder, mainNet);
    s1 = builder.toString();
    s2 = _formatKey(key, true, mainNet);
    checkEquals(s1,s2, "checkFormatKeyWithAddress.2");
  }

  public void checkFromASN1(){
    ECKey k1 = new ECKey();  
    byte[] asn1 = k1.toASN1();
    ECKey k2 = ECKey.fromASN1(asn1);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n2 = k2.getPrivKey();
    checkEquals(n1, n2, "checkFromASN1.1");
  }

  public void checkFromEncrypted(){
    ECKey k1 = new ECKey();
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);
    EncryptedData data = k2.getEncryptedData();
    byte[] pubkey = k2.getPubKey();
    ECKey k3 = ECKey.fromEncrypted(data, crypter, pubkey);
    ECKey k4 = k3.decrypt(aesKey);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n4 = k4.getPrivKey();
    checkEquals(n1, n4, "checkFromEncrypted.1");
  }

  public void checkFromPrivateFromBigInteger(){
    ECKey key = ECKey.fromPrivate(secret1); // compressed by default  
    checkCondition(isKeyFromSecret1(key), "checkFromPrivateFromBigInteger.1");
    checkCondition(key.isCompressed(), "checkFromPrivateFromBigInteger.2");
  }

  public void checkFromPrivateFromBigIntegerBool(){
    // compressed
    ECKey key = ECKey.fromPrivate(secret1, true); // compressed = true 
    checkCondition(isKeyFromSecret1(key), "checkFromPrivateFromBigIntegerBool.1");
    checkCondition(key.isCompressed(), "checkFromPrivateFromBigIntegerBool.2");
    // uncompressed
    key = ECKey.fromPrivate(secret1, false);      // compressed = false
    checkCondition(isKeyFromSecret1(key), "checkFromPrivateFromBigIntegerBool.3");
    checkCondition(!key.isCompressed(), "checkFromPrivateFromBigIntegerBool.4");
  }

  public void checkFromPrivateFromBytes(){
    ECKey k1 = new ECKey();
    byte[] priv = k1.getPrivKeyBytes();
    ECKey k2 = ECKey.fromPrivate(priv);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n2 = k2.getPrivKey();
    checkEquals(n1, n2, "checkFromPrivateFromBytes.1");
  }

  public void checkFromPrivateFromBytesBool(){
    // compressed
    ECKey k1 = new ECKey();
    byte[] priv = k1.getPrivKeyBytes();
    ECKey k2 = ECKey.fromPrivate(priv, true);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n2 = k2.getPrivKey();
    checkEquals(n1, n2, "checkFromPrivateFromBytes.1");
    checkCondition(k2.isCompressed(),"checkFromPrivateBytes.2");
    // uncompressed
    ECKey k3 = ECKey.fromPrivate(priv, false);
    BigInteger n3 = k3.getPrivKey();
    checkEquals(n1, n3, "checkFromPrivateFromBytes.3");
    checkCondition(!k3.isCompressed(),"checkFromPrivateBytes.4");
  }

  public void checkFromPrivateAndPrecalculatedPublic(){
    ECKey k1 = new ECKey();
    BigInteger n1 = k1.getPrivKey();
    ECPoint p1 = k1.getPubKeyPoint();
    ECKey k2 = ECKey.fromPrivateAndPrecalculatedPublic(n1,p1);
    BigInteger n2 = k2.getPrivKey();
    checkEquals(n1, n2, "checkFromPrivateAndPrecalculatedPublic.1");
    ECPoint p2 = k2.getPubKeyPoint();
    checkEquals(p1, p2, "checkFromPrivateAndPrecalculatedPublic.2");
    checkCondition(
        k2.isCompressed(), 
        "checkFromPrivateAndPrecalculatedPublic.3"
    );
 
  }

  public void checkFromPrivateAndPrecalculatedPublicFromBytes(){
    // compressed
    ECKey k1 = new ECKey();
    byte[] priv1 = k1.getPrivKeyBytes();
    byte[] pub1 = k1.getPubKey();
    ECKey k2 = ECKey.fromPrivateAndPrecalculatedPublic(priv1,pub1);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n2 = k2.getPrivKey();
    checkEquals(n1, n2, "checkFromPrivateAndPrecalculatedPublicFromBytes.1");
    ECPoint p1 = k1.getPubKeyPoint();
    ECPoint p2 = k2.getPubKeyPoint();
    checkEquals(p1, p2, "checkFromPrivateAndPrecalculatedPublicFromBytes.2");
    checkCondition(
        k2.isCompressed(), 
        "checkFromPrivateAndPrecalculatedPublicFromBytes.3"
    );
    // uncompressed
    ECKey k3 = k1.decompress();
    byte[] priv3 = priv1;
    byte[] pub3 = k3.getPubKey();
    ECKey k4 = ECKey.fromPrivateAndPrecalculatedPublic(priv3,pub3);
    BigInteger n3 = k3.getPrivKey();
    BigInteger n4 = k4.getPrivKey();
    checkEquals(n3, n4, "checkFromPrivateAndPrecalculatedPublicFromBytes.4");
    ECPoint p3 = k3.getPubKeyPoint();
    ECPoint p4 = k4.getPubKeyPoint();
    checkEquals(p3, p4, "checkFromPrivateAndPrecalculatedPublicFromBytes.5");
    checkCondition(
        !k4.isCompressed(), 
        "checkFromPrivateAndPrecalculatedPublicFromBytes.6"
    );
  }

  public void checkFromPublicOnlyFromBytes(){
    ECKey k1 = new ECKey();
    byte[] pubkey = k1.getPubKey();
    ECKey k2 = ECKey.fromPublicOnly(pubkey);
    ECPoint p1 = k1.getPubKeyPoint();
    ECPoint p2 = k2.getPubKeyPoint();
    checkEquals(p1, p2, "checkFromPublicOnlyFromBytes.1");
    checkCondition(!k2.hasPrivKey(),"checkFromPublicOnlyFromBytes.2");
    checkCondition(!k2.isEncrypted(),"checkFromPublicOnlyFromBytes.3");
    checkCondition(k2.isPubKeyOnly(),"checkFromPublicOnlyFromBytes.4");
    checkCondition(k2.isWatching(),"checkFromPublicOnlyFromBytes.5");
  }

  public void checkFromPublicOnly(){
    ECKey k1 = new ECKey();
    ECPoint p1 = k1.getPubKeyPoint();
    ECKey k2 = ECKey.fromPublicOnly(p1);
    ECPoint p2 = k2.getPubKeyPoint();
    checkEquals(p1, p2, "checkFromPublicOnly.1");
    checkCondition(!k2.hasPrivKey(),"checkFromPublicOnly.2");
    checkCondition(!k2.isEncrypted(),"checkFromPublicOnly.3");
    checkCondition(k2.isPubKeyOnly(),"checkFromPublicOnly.4");
    checkCondition(k2.isWatching(),"checkFromPublicOnly.5");
  }



  public void checkGetCreationTimeSeconds(){
    ECKey key = new ECKey();
    long time = key.getCreationTimeSeconds();  
    Date date = new Date();
    long current = date.getTime()/1000;       // getTime() in milliseconds
    checkCondition(time <= current, "checkGetCreationTimeSeconds.1");
    // should not be more than one second apart
    checkCondition(Math.abs(time - current) < 1, "checkGetCreationTimeSeconds.2");
  }

  public void checkGetEncryptedData(){
    ECKey k1 = new ECKey();
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);
    EncryptedData data = k2.getEncryptedData();
    byte[] pubkey = k2.getPubKey();
    ECKey k3 = ECKey.fromEncrypted(data, crypter, pubkey);
    ECKey k4 = k3.decrypt(aesKey);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n4 = k4.getPrivKey();
    checkEquals(n1, n4, "checkGetEncryptedData.1");
  }

  public void checkGetEncryptedPrivateKey(){
    ECKey k1 = new ECKey();
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);
    EncryptedData data = k2.getEncryptedPrivateKey();
    byte[] pubkey = k2.getPubKey();
    ECKey k3 = ECKey.fromEncrypted(data, crypter, pubkey);
    ECKey k4 = k3.decrypt(aesKey);
    BigInteger n1 = k1.getPrivKey();
    BigInteger n4 = k4.getPrivKey();
    checkEquals(n1, n4, "checkGetEncryptedPrivateKey.1");
  }

  public void checkGetEncryptionType(){
    ECKey k1 = new ECKey ();
    checkCondition(
        k1.getEncryptionType() == EncryptionType.UNENCRYPTED, 
        "checkGetEncryptionType.11"
    );
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some random passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);
    checkCondition(
        k2.getEncryptionType() == EncryptionType.ENCRYPTED_SCRYPT_AES,
        "checkGetEncryptionType.2"
    );
  }

  public void checkGetKeyCrypter(){
    ECKey k1 = new ECKey ();
    KeyCrypter crypt1 = new KeyCrypterScrypt();
    KeyParameter aesKey = crypt1.deriveKey("some random passphrase");
    ECKey k2 = k1.encrypt(crypt1, aesKey);
    KeyCrypter crypt2 = k2.getKeyCrypter();
    checkEquals(crypt1, crypt2, "checkGetKeyCrypter.1");
  }


  public void checkGetPrivateKeyAsHex(){
    // key1
    checkEquals(
        secret1AsHex.toLowerCase(), 
        key1.getPrivateKeyAsHex().toLowerCase(), 
        "checkGetPrivateKeyAsHex.1"
    );
    // random key
    ECKey key = new ECKey();
    byte[] priv = key.getPrivKeyBytes();
    String hex1 = DatatypeConverter.printHexBinary(priv).toLowerCase();
    String hex2 = key.getPrivateKeyAsHex();
    checkEquals(hex1, hex2, "checkGetPrivateKeyAsHex.2");
  }

  public void checkGetPrivateKeyAsWiF(){
    // key1 compressed on main network
    String check1 = key1.getPrivateKeyAsWiF(mainNet);
    checkEquals(check1, secret1AsWiF, "checkGetPrivateKeyAsWiF.1");
    // key1 uncompressed on main network
    String check2 = key1Uncomp.getPrivateKeyAsWiF(mainNet);
    checkEquals(check2, secret1AsWiFUncomp, "checkGetPrivateKeyAsWiF.2");
    // key1 compressed on test network
    String check3 = key1.getPrivateKeyAsWiF(regTestNet);
    checkEquals(check3, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.3");
    // key1 uncompressed on test network
    String check4 = key1Uncomp.getPrivateKeyAsWiF(regTestNet);
    checkEquals(check4, secret1AsWiFTestUncomp, "checkGetPrivateKeyAsWiF.4");


    // All three testing networks give same WiF output (compressed)
    String check5 = key1.getPrivateKeyAsWiF(regTestNet);
    checkEquals(check5, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.5");

    String check6 = key1.getPrivateKeyAsWiF(testNetNet);
    checkEquals(check6, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.6");

    String check7 = key1.getPrivateKeyAsWiF(unitTestNet);
    checkEquals(check7, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.7");
    
    // All three testing networks give same WiF output (uncompressed)
    String check8 = key1Uncomp.getPrivateKeyAsWiF(regTestNet);
    checkEquals(check8, secret1AsWiFTestUncomp, "checkGetPrivateKeyAsWiF.8");

    String check9 = key1Uncomp.getPrivateKeyAsWiF(testNetNet);
    checkEquals(check9, secret1AsWiFTestUncomp, "checkGetPrivateKeyAsWiF.9");

    String check10 = key1Uncomp.getPrivateKeyAsWiF(unitTestNet);
    checkEquals(check10, secret1AsWiFTestUncomp, "checkGetPrivateKeyAsWiF.10");

    // random key
    // checking output coincides with that of toString method on the
    // DumpedPrivateKey object returned by getPrivateKeyEncoded.
    // Hence getPrivateKeyEncoded needs to be validated as well 
    // as toString method on DumpedPrivateKey object.
    
    ECKey key = new ECKey();

    String wif1 = key.getPrivateKeyAsWiF(mainNet);
    String wif2 = key.getPrivateKeyEncoded(mainNet).toString();
    checkEquals(wif1, wif2, "checkGetPrivateKeyAsWiF.5");

    String wif3 = key.getPrivateKeyAsWiF(regTestNet);
    String wif4 = key.getPrivateKeyEncoded(regTestNet).toString();
    checkEquals(wif3, wif4, "checkGetPrivateKeyAsWiF.6");

    String wif5 = key.getPrivateKeyAsWiF(testNetNet);
    String wif6 = key.getPrivateKeyEncoded(testNetNet).toString();
    checkEquals(wif5, wif6, "checkGetPrivateKeyAsWiF.7");

    String wif7 = key.getPrivateKeyAsWiF(unitTestNet);
    String wif8 = key.getPrivateKeyEncoded(unitTestNet).toString();
    checkEquals(wif5, wif6, "checkGetPrivateKeyAsWiF.8");
    
  }

  public void checkGetPrivateKeyEncoded(){
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();


    // commong secret
    BigInteger secret = k1.getPrivKey();
    checkEquals(secret, k2.getPrivKey(), "checkGetPrivateKeyEncoded.1");

    // public keys
    byte[] pubkey1 = k1.getPubKey();
    byte[] pubkey2 = k2.getPubKey();

    // creating DumpedPrivateKey from k1 and k2
    DumpedPrivateKey dpkMain1 = k1.getPrivateKeyEncoded(mainNet); 
    DumpedPrivateKey dpkMain2 = k2.getPrivateKeyEncoded(mainNet); 
    DumpedPrivateKey dpkTest1 = k1.getPrivateKeyEncoded(regTestNet); 
    DumpedPrivateKey dpkTest2 = k2.getPrivateKeyEncoded(regTestNet); 

    // retrieving ECKey's from DumpedPrivateKey's
    ECKey keyMain1 = dpkMain1.getKey();
    ECKey keyMain2 = dpkMain2.getKey();
    ECKey keyTest1 = dpkTest1.getKey();
    ECKey keyTest2 = dpkTest2.getKey();

    // checking private keys
    logMessage("-> ECKey::getPrivateKeyEncoded see unit testing code ... ");
//    checkEquals(secret, keyMain1.getPrivKey(), "checkGetPrivateKeyEncoded.2");
    checkEquals(secret, keyMain2.getPrivKey(), "checkGetPrivateKeyEncoded.3");
//    checkEquals(secret, keyTest1.getPrivKey(), "checkGetPrivateKeyEncoded.4");
    checkEquals(secret, keyTest2.getPrivKey(), "checkGetPrivateKeyEncoded.5");

    // checking compression status
    checkCondition(keyMain1.isCompressed(), "checkGetPrivateKeyEncoded.6");
    checkCondition(!keyMain2.isCompressed(), "checkGetPrivateKeyEncoded.7");
    checkCondition(keyTest1.isCompressed(), "checkGetPrivateKeyEncoded.8");
    checkCondition(!keyTest2.isCompressed(), "checkGetPrivateKeyEncoded.9");

    // checking public keys
    boolean chkMain1 = Arrays.equals(pubkey1, keyMain1.getPubKey());
    boolean chkMain2 = Arrays.equals(pubkey2, keyMain2.getPubKey());
    boolean chkTest1 = Arrays.equals(pubkey1, keyTest1.getPubKey());
    boolean chkTest2 = Arrays.equals(pubkey2, keyTest2.getPubKey());

//    checkCondition(chkMain1, "checkGetPrivateKeyEncoded.10");
    checkCondition(chkMain2, "checkGetPrivateKeyEncoded.11");
//    checkCondition(chkTest1, "checkGetPrivateKeyEncoded.12");
    checkCondition(chkTest2, "checkGetPrivateKeyEncoded.13");
  }


  public void checkGetPrivKey(){
    checkEquals(key1.getPrivKey(), secret1, "checkGetPrivKey.1");
    BigInteger secret = getRandomSecret();
    ECKey key = ECKey.fromPrivate(secret);
    checkEquals(key.getPrivKey(), secret, "checkGetPrivKey.2");
  }

  public void checkGetPrivKeyBytes(){

    // check in key1
    byte[] check = key1.getPrivKeyBytes();
    checkEquals(check.length,32, "checkPrivKeyBytes.1");
    int length = secret1AsBytes.length;
    for(int i = 0; i < length; ++i){
      checkEquals(check[i],secret1AsBytes[i],"checkPrivKeyBytes.2"); 
    }

    // check on random key
    BigInteger secret = getRandomSecret();
    ECKey key = ECKey.fromPrivate(secret);
    check = key.getPrivKeyBytes();
    BigInteger n = new BigInteger(1, check); // decoding bytes back into secret
    checkEquals(secret, n, "checkPrivKeyBytes.3");
  }

  public void checkGetPubKey(){
    // checking key1 compressed
    byte[] check = key1.getPubKey();
    BigInteger n = new BigInteger(1, check);
    checkEquals(n, secret1PubKey, "checkGetPubKey.1");
    // checking key1 uncompressed
    check = key1Uncomp.getPubKey();
    n = new BigInteger(1, check);
    checkEquals(n, secret1PubKeyUncomp, "checkGetPubKey.2");

    // random key
    for(int i = 0; i < 256; ++i){
      ECKey k1 = new ECKey();
      ECKey k2 = k1.decompress();

      byte[] pubkey1 = k1.getPubKey();
      byte[] pubkey2 = k2.getPubKey();

      ECPoint point1 = k1.getPubKeyPoint();
      ECPoint point2 = k2.getPubKeyPoint();
      checkEquals(point1, point2, "checkGetPubKey.3");

      byte[] byteX = point1.getAffineXCoord().getEncoded();
      byte[] byteY = point1.getAffineYCoord().getEncoded();

      boolean isEven = _isEven(new BigInteger(1, byteY)); 

      byte[] pubkey4 = new byte[65]; // uncompressed

      // setting up compressed public key
      byte[] pubkey3 = new byte[33]; // compressed
      pubkey3[0] = isEven ? (byte) 0x02 : (byte) 0x03;
      System.arraycopy(byteX, 0, pubkey3, 1, 32);

      // setting up uncompressed key
      pubkey4[0] = (byte) 0x04;
      System.arraycopy(byteX, 0, pubkey4, 1, 32);
      System.arraycopy(byteY, 0, pubkey4, 33, 32);

      // checking public keys
      checkCondition(Arrays.equals(pubkey1, pubkey3), "checkPubKey.4");
      checkCondition(Arrays.equals(pubkey2, pubkey4), "checkPubKey.5");

      // we can actually perform a validation of Y given X
      BigInteger x = new BigInteger(1, byteX);
      BigInteger y = new BigInteger(1, byteY);
      BigInteger z = YFromX(x, isEven);
      checkEquals(y, z, "checkPubKey.6");
    }
  }

  public void checkGetPubKeyHash(){
    // checking key1 compressed
    byte[] check = key1.getPubKeyHash();
    BigInteger n = new BigInteger(1, check);  // unsigned
    checkEquals(n, secret1PubKeyHash, "checkGetPubKeyHash.1");
    // checking key1 uncompressed
    check = key1Uncomp.getPubKeyHash();
    n = new BigInteger(1, check);
    checkEquals(n, secret1PubKeyHashUncomp, "checkGetPubKeyHash.2");
    // random key
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();

    byte[] hash1 = k1.getPubKeyHash();
    byte[] hash2 = k2.getPubKeyHash();

    byte[] sha1 = Sha256Hash.hash(k1.getPubKey());
    byte[] sha2 = Sha256Hash.hash(k2.getPubKey());

    byte[] hash3 = _ripemd160(sha1);
    byte[] hash4 = _ripemd160(sha2);

    checkCondition(Arrays.equals(hash1, hash3), "checkGetPubKeyHash.1");
    checkCondition(Arrays.equals(hash2, hash4), "checkGetPubKeyHash.2");
  }

  public void checkGetPubKeyPoint(){
    // key1 compressed
    ECPoint point = key1.getPubKeyPoint();
    checkCondition(point.isNormalized(), "checkGetPubKeyPoint.1");
    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();
    checkEquals(x, secret1PubKeyX, "checkGetPubKeyPoint.2");
    checkEquals(y, secret1PubKeyY, "checkGetPubKeyPoint.3");
    // key1 uncompressed
    checkEquals(point, key1Uncomp.getPubKeyPoint(), "checkGetPubKeyPoint.4");
    // random key
    ECKey key = new ECKey();
    point = key.getPubKeyPoint();
    checkCondition(point.isNormalized(), "checkGetPubKeyPoint.5");
    x = point.getAffineXCoord().toBigInteger();
    y = point.getAffineYCoord().toBigInteger();
    byte[] bytes = key.getPubKey();
    checkEquals(bytes.length, 33, "checkGetPubKeyPoint.6");
    checkCondition(
        bytes[0] == (byte) 0x03 || bytes[0] == (byte) 0x02,
        "checkGetPubKeyPoint.7");
    // creating unsigned BigInteger from byte 1 (inclusive) to byte 33 (exclusive)
    BigInteger xx = new BigInteger(1, Arrays.copyOfRange(bytes,1,33));
    checkEquals(x, xx, "checkGetPubKeyPoint.8");
    boolean isEven = (bytes[0] == (byte) 0x02);
    BigInteger yy = YFromX(x, isEven);
    checkEquals(y, yy, "checkGetPubKeyPoint.9");
    // TODO actually validate ECPoint from secret, not using getPubKey.
  }

  public void checkGetPublicKeyAsHex(){
    // key1 compressed
    String check = key1.getPublicKeyAsHex();
    BigInteger n = new BigInteger(check, 16);
    checkEquals(n, secret1PubKey, "checkGetPublicKeyAsHex.1");
    // key1 uncompressed
    check = key1Uncomp.getPublicKeyAsHex();
    n = new BigInteger(check, 16);
    checkEquals(n, secret1PubKeyUncomp, "checkPublicKeyAsHex.2");
    // random compressed key
    ECKey key = new ECKey();
    check = key.getPublicKeyAsHex();
    n = new BigInteger(check, 16);
    byte[] bytes = key.getPubKey();
    // compressed public key has 33 bytes
    checkEquals(bytes.length, 33, "checkGetPublicKeyAsHex.3");
    BigInteger m = new BigInteger(1, bytes);
    checkEquals(n, m, "checkGetPublicKeyAsHex.4");
    // random uncompressed key
    BigInteger secret = getRandomSecret();
    key = ECKey.fromPrivate(secret, false);
    check = key.getPublicKeyAsHex();
    n = new BigInteger(check, 16);
    bytes = key.getPubKey();
    // uncompressed public key has 65 bytes
    checkEquals(bytes.length, 65, "checkGetPublicKeyAsHex.5");
    m = new BigInteger(1, bytes);
    checkEquals(n, m, "checkGetPublicKeyAsHex.6");
  }

  // same checks as those of getPrivKeyBytes
  public void checkGetSecretBytes(){
    // check in key1
    byte[] check = key1.getSecretBytes();
    checkEquals(check.length,32, "checkGetSecretBytes.1");
    int length = secret1AsBytes.length;
    for(int i = 0; i < length; ++i){
      checkEquals(check[i],secret1AsBytes[i],"checkGetSecretBytes.2"); 
    }
    // check on random key
    BigInteger secret = getRandomSecret();
    ECKey key = ECKey.fromPrivate(secret);
    check = key.getSecretBytes();
    BigInteger n = new BigInteger(1, check); // decoding bytes back into secret
    checkEquals(secret, n, "checkGetSecretBytes.3");

  }

  public void checkHashCode(){
    // TODO
  }

  public void checkHasPrivKey(){
    // key1
    checkCondition(key1.hasPrivKey(), "checkHashPrivKey.1");
    checkCondition(key1Uncomp.hasPrivKey(), "checkHashPrivKey.2");
    // random 
    ECKey key = new ECKey();
    checkCondition(key.hasPrivKey(), "checkHashPrivKey.3");
    // TODO check on encrypted key
    // TODO check on public only key
  }

  public void checkIsCompressed(){
    checkCondition(key1.isCompressed(), "checkIsCompressed.1");
    checkCondition(!key1Uncomp.isCompressed(), "checkIsCompressed.2");
    ECKey key = new ECKey();  // compressed by default
    checkCondition(key.isCompressed(), "checkIsCompressed.3");
    BigInteger secret = getRandomSecret();
    key = ECKey.fromPrivate(secret, true);  // compressed
    checkCondition(key.isCompressed(), "checkIsCompressed.4");
    key = ECKey.fromPrivate(secret, false);  // uncompressed
    checkCondition(!key.isCompressed(), "checkIsCompressed.5");
  }

  public void checkIsEncrypted(){
    checkCondition(!key1.isEncrypted(), "checkIsEncrypted.1");
    checkCondition(!key1Uncomp.isEncrypted(), "checkIsEncrypted.2");
    ECKey key = new ECKey();  // not encrypted by default
    checkCondition(!key.isEncrypted(), "checkIsEncrypted.3");
    // TODO check on encrypted key
  }

  public void checkIsPubKeyCanonical(){
    // compressed public key
    byte[] pubkey = key1.getPubKey();
    checkCondition(ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.1");
    checkEquals(pubkey[0], (byte) 0x03, "checkIsPubKeyCanonical.2");
    // changing parity in compressed public key should maintain canonicity
    pubkey[0] = (byte) 0x02;
    checkCondition(ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.3");
    // but if first byte is not 0x03 or 0x02 then... 
    pubkey[0] = (byte) 0x04;  // shouldn't be allowed for compressed key
    checkCondition(!ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.4");
    // uncompressed
    pubkey = key1Uncomp.getPubKey();
    checkCondition(ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.5");
    checkEquals(pubkey[0], (byte) 0x04, "checkIsPubKeyCanonical.6");
    pubkey[0] = (byte) 0x02;  // shouldn't be allowed for uncompressed key
    checkCondition(!ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.7");
    pubkey[0] = (byte) 0x03;  // shouldn't be allowed for uncompressed key
    checkCondition(!ECKey.isPubKeyCanonical(pubkey), "checkIsPubKeyCanonical.8");
  }

  public void checkIsPubKeyOnly(){
    checkCondition(!key1.isPubKeyOnly(), "checkIsPubKeyOnly.1");
    checkCondition(!key1Uncomp.isPubKeyOnly(), "checkIsPubKeyOnly.2");
    // TODO check on encrypted key
    // TODO check on public only key
  }

  public void checkIsWatching(){
    checkCondition(!key1.isWatching(), "checkIsWatching.1");
    checkCondition(!key1Uncomp.isWatching(), "checkIsWatching.1");
    // TODO check on encrypted key
    // TODO check on public only key
  }

  public void checkMaybeDecrypt(){
    // TODO
  }

  public void checkPublicKeyFromPrivate(){
    // compressed
    byte[] pubkey1 = ECKey.publicKeyFromPrivate(secret1, true);
    byte[] pubkey2 = key1.getPubKey();
    checkEquals(pubkey1.length, 33, "checkPublicKeyFromPrivate.1");
    checkEquals(pubkey2.length, 33, "checkPublicKeyFromPrivate.2");
    for(int i = 0; i < 33; ++i){
      checkEquals(pubkey1[i], pubkey2[i], "checkPublicKeyFromPrivate.3");
    }
    // uncompressed
    pubkey1 = ECKey.publicKeyFromPrivate(secret1, false);
    pubkey2 = key1Uncomp.getPubKey();
    checkEquals(pubkey1.length, 65, "checkPublicKeyFromPrivate.4");
    checkEquals(pubkey2.length, 65, "checkPublicKeyFromPrivate.5");
    for(int i = 0; i < 65; ++i){
      checkEquals(pubkey1[i], pubkey2[i], "checkPublicKeyFromPrivate.6");
    }

    // random key, compressed
    BigInteger secret = getRandomSecret();
    pubkey1 = ECKey.publicKeyFromPrivate(secret, true);
    ECPoint point = ECKey.publicPointFromPrivate(secret); // tested elsewhere
    point = point.normalize();  
    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();
    BigInteger two = BigInteger.ONE.shiftLeft(1);
    boolean isEven = (y.mod(two) == BigInteger.ZERO);
    byte first = isEven ? (byte) 0x02 : (byte) 0x03;
    // checking first byte of compressed public key
    checkEquals(first, pubkey1[0], "checkPublicKeyFromPrivate.7");
    // checking remaining bytes of compressed public key
    BigInteger xx = new BigInteger(1, Arrays.copyOfRange(pubkey1,1,33)); 
    checkEquals(x,xx, "checkPublicKeyFromPrivate.8");
    
    // random key, uncompressed
    pubkey1 = ECKey.publicKeyFromPrivate(secret, false);
    // checking first byte of uncompressed public key 
    checkEquals((byte) 0x04, pubkey1[0], "checkPublicKeyFromPrivate.8");
    // checking remaining bytes of uncompressed public key 
    xx = new BigInteger(1, Arrays.copyOfRange(pubkey1,1,33));
    BigInteger yy = new BigInteger(1, Arrays.copyOfRange(pubkey1,33,65));
    checkEquals(x,xx,"checkPublicKeyFromPrivate.9");
    checkEquals(y,yy,"checkPublicKeyFromPrivate.10");
  }

  // main primitive
  public void checkPublicPointFromPrivate(){
    ECPoint point1 = ECKey.publicPointFromPrivate(secret1);
    point1 = point1.normalize();
    ECPoint point2 = key1.getPubKeyPoint();
    checkCondition(point2.isNormalized(), "checkPublicPointFromPrivate.1");
    BigInteger x1 = point1.getAffineXCoord().toBigInteger();
    BigInteger y1 = point1.getAffineYCoord().toBigInteger();
    BigInteger x2 = point2.getAffineXCoord().toBigInteger();
    BigInteger y2 = point2.getAffineYCoord().toBigInteger();
    checkEquals(x1, x2, "checkPublicPointFromPrivate.2");
    checkEquals(y1, y2, "checkPublicPointFromPrivate.2");
    // TODO random secret
  }

  public void checkRecoverFromSignature(){
    // TODO
  }

  public void checkSetCreationTimeSeconds(){
    ECKey key = new ECKey();  // random, compressed
    long time1 = key.getCreationTimeSeconds() - 1000;
    key.setCreationTimeSeconds(time1);
    long time2 = key.getCreationTimeSeconds();
    checkEquals(time1, time2, "checkSetCreationTimeSeconds.1");
  }

  public void checkSign(){
    // TODO
  }

  public void checkSignFromKeyParameter(){
    // TODO
  }

  public void checkSignedMessageToKey(){
    // TODO
  }

  public void checkSignMessage(){
    // TODO
  }

  public void checkSignMessageFromKeyParameter(){
    // TODO
  }

  public void checkToAddress(){
    // key1 compressed
    String check = key1.toAddress(mainNet).toString();
    checkEquals(check, secret1Address, "checkToAddress.1");

    // key1 uncompressed
    check = key1Uncomp.toAddress(mainNet).toString();
    checkEquals(check, secret1AddressUncomp, "checkToAddress.2");

    // TODO random key compressed/uncompressed various networks

  }

  public void checkToASN1(){
    // key1
    byte[] bytes = key1.toASN1();
    ECKey key = ECKey.fromASN1(bytes);
    checkCondition(isKeyFromSecret1(key), "checkToASN1.1");
    // TODO properly check ASN1 encoding on random key
  }

  public void checkToString(){
    // key1 compressed
    checkEquals(key1.toString(), _toString(key1), "checkToString.1");
    // key1 uncompressed
    checkEquals(key1Uncomp.toString(), _toString(key1Uncomp), "checkToString.2");

    // random key compressed
    ECKey key = new ECKey();
    key.setCreationTimeSeconds(0);  // suppress display of creation time
    checkEquals(key.toString(), _toString(key), "checkToString.3");
    // random key uncompressed
    BigInteger secret = getRandomSecret();
    key = ECKey.fromPrivate(secret, false);
    checkEquals(key.toString(), _toString(key), "checkToString.4");

    // TODO could add time creation time
    // TODO check encrypted key
    // TODO check PubKeyOnly
  }

  public void checkToStringWithPrivate(){
    // key compressed, main network
    checkEquals(
        key1.toStringWithPrivate(mainNet), 
        _toStringWithPrivate(key1,mainNet),
        "checkToStringWithPrivate.1"
    );

    // key compressed, RegTest network
    checkEquals(
        key1.toStringWithPrivate(regTestNet), 
        _toStringWithPrivate(key1,regTestNet),
        "checkToStringWithPrivate.2"
    );
    // random key compressed
    ECKey key = new ECKey();
    key.setCreationTimeSeconds(0);  // suppress display of creation time
    checkEquals(
        key.toStringWithPrivate(mainNet), 
        _toStringWithPrivate(key,mainNet), 
        "checkToStringWithPrivate.3"
    );

    // TODO see toString
 
  }

  public void checkVerify(){
    // TODO
  }

  public void checkVerifyFromPubKeySigAsBytes(){
    // TODO
  }

  public void checkVerifyFromPubKey(){
    // TODO
  }

  public void checkVerifyHash(){
    // TODO
  }

  public void checkVerifyMessage(){
    // TODO
  }

  public void checkVerifyOrThrow(){
    // TODO
  }

  public void checkVerifyOrThrowSigAsBytes(){
    // TODO
  }

}

