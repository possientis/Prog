import java.util.Comparator;
import java.util.Date;
import java.util.Arrays;
import java.math.BigInteger;
import java.lang.Math;
import java.security.SecureRandom;

import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.wallet.Protos.Wallet.EncryptionType;


import org.spongycastle.crypto.params.ECDomainParameters;
import org.spongycastle.math.ec.ECPoint;


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
    checkEquals();
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
    return "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ";
  }

  private String getSecret1AsWiFTest(){
    // TODO obtain independent confirmation for this string
    return "cNcBUemoNGVRN9fRtxrmtteAPQeWZ399d2REmX1TBjvWpRfNMy91";
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


  private NetworkParameters getMainNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_MAINNET);
  }

  private NetworkParameters getRegTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_REGTEST);
  }

  private NetworkParameters getTestNetNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_TESTNET);
  }

  private NetworkParameters getUnitTestNetwork(){
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
  private final String secret1AsWiFTest = getSecret1AsWiFTest();
  private final String secret1PubKeyXAsHex = getSecret1PubKeyXAsHex();
  private final String secret1PubKeyYAsHex = getSecret1PubKeyYAsHex();
  private final String secret1PubKeyAsHex = getSecret1PubKeyAsHex();
  private final String secret1PubKeyUncompAsHex = getSecret1PubKeyUncompAsHex();
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
    if (key.getPrivKey() != secret1) return false;
    // TODO possibly other validations here
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
    checkEquals(half, halfCurveOrder, "checkHalfCurveOrder");
  }

  // checking static fiels FAKE_SIGNATURES
  public void checkFakeSignatures(){
    boolean flag = ECKey.FAKE_SIGNATURES;
    checkEquals(flag, false, "checkFakeSignatures");
  }

  // checking static field PUBKEY_COMPARATOR
  public void checkPubKeyComparator(){
    Comparator<ECKey> comp = ECKey.PUBKEY_COMPARATOR;
  }

  public void checkConstructorDefault(){
    ECKey key = new ECKey();  // generate new keypair
    checkNotNull(key, "checkConstructorDefault");
  }

  public void checkConstructorFromSecureRandom(){
    ECKey key = new ECKey(random);
    checkNotNull(key, "checkConstructorFromSecureRandom");
  }

  public void checkCompressPoint(){
    // TODO
  }

  public void checkCompressPointLazy(){
    // TODO
  }

  public void checkDecompress(){
    // TODO
  }
  
  public void checkDecompressPoint(){
    // TODO
  }

  public void checkDecompressPointLazy(){
    // TODO
  }

  public void checkDecrypt(){
    // TODO
  }

  public void checkDecryptFromKeyCrypter(){
    // TODO
  }

  public void checkEncrypt(){
    // TODO
  }

  public void checkEncryptionIsReversible(){
    // TODO
  }

  public void checkEquals(){
    // TODO
  }

  public void checkFormatKeyWithAddress(){
    // TODO
  }

  public void checkFromASN1(){
    // TODO
  }

  public void checkFromEncrypted(){
    // TODO
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
    // TODO
  }

  public void checkFromPrivateFromBytesBool(){
    // TODO
  }

  public void checkFromPrivateAndPrecalculatedPublic(){
    // TODO
  }

  public void checkFromPrivateAndPrecalculatedPublicFromBytes(){
    // TODO
  }

  public void checkFromPublicOnly(){
    // TODO
  }

  public void checkFromPublicOnlyFromBytes(){
    // TODO
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
    // TODO
  }

  public void checkGetEncryptedPrivateKey(){
    // TODO
  }

  public void checkGetEncryptionType(){
    checkCondition(
        key1.getEncryptionType() == EncryptionType.UNENCRYPTED, 
        "checkGetEncryptionType"
    );

    // TODO more validation
  }

  public void checkGetKeyCrypter(){
    // TODO
  }


  public void checkGetPrivateKeyAsHex(){
    checkEquals(
        secret1AsHex.toLowerCase(), 
        key1.getPrivateKeyAsHex().toLowerCase(), 
        "checkGetPrivateKeyAsHex.1"
    );

    ECKey key = new ECKey(); // random, test cannot be replicated
    String check = key.getPrivKey().toString(16);
    // Comparing check with key.getPrivateKeyAsHex() may fail because
    // of leading 0' which will not appear in output of toString.
    // Converting these strings to numbers should allow us to compare
    BigInteger n1 = new BigInteger(check,16);
    BigInteger n2 = new BigInteger(key.getPrivateKeyAsHex(),16);
    checkEquals(n1, n2, "checkGetPrivateKeyAsHex.2");
  }

  public void checkGetPrivateKeyAsWiF(){
    String checkMain = key1.getPrivateKeyAsWiF(mainNet);
    checkEquals(checkMain, secret1AsWiF, "checkGetPrivateKeyAsWiF.1");

    // All three testing networks give same WiF output
    String checkRegTest = key1.getPrivateKeyAsWiF(regTestNet);
    checkEquals(checkRegTest, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.2");

    String checkTestNet = key1.getPrivateKeyAsWiF(testNetNet);
    checkEquals(checkTestNet, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.3");

    String checkUnitTest = key1.getPrivateKeyAsWiF(unitTestNet);
    checkEquals(checkUnitTest, secret1AsWiFTest, "checkGetPrivateKeyAsWiF.4");

    // TODO additional validation on random key
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

    // TODO need compressed key with even parity
    // TODO check on random compressed key
    // TODO check on random uncompressed key
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
    // TODO check on random compressed
    // TODO check on random uncompressed
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
    ECKey key = new ECKey();
    logMessage(key.signMessage("Hello world!"));
  }

  public void checkSignMessageFromKeyParameter(){
    // TODO
  }


}

