import java.util.Comparator;
import java.util.Date;
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

  private boolean isKeyFromSecret1(ECKey key){
    if (key.getPrivKey() != secret1) return false;
    // TODO possibly other validations here
    return true;
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

  // data derived from independent sources
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
    // waiting a second before creating new key
    try {
      Thread.sleep(1000);
    } catch (Exception e){
      checkCondition(false, "checkAgeComparator.1");
    }

    ECKey k2 = new ECKey(); // at least a second older

    checkCondition(comp.compare(k1,k1) == 0, "checkAgeComparator.2");
    checkCondition(comp.compare(k2,k2) == 0, "checkAgeComparator.3");
    checkCondition(comp.compare(k1,k2) < 0, "checkAgeComparator.4");
    checkCondition(comp.compare(k2,k1) > 0, "checkAgeComparator.5");
  }

  // checking static field CURVE
  public void checkCurve(){
    // TODO checking value of field underlying prime number
    ECDomainParameters curve = ECKey.CURVE;
    // getN() method returns order of elliptic curve
    checkEquals(curve.getN(), curveOrder, "checkCurve");
    // getH() method returns the 'cofactor' of elliptic curve (should be 1)
    checkEquals(curve.getH(), BigInteger.ONE, "checkCurve");
    // getG() method returns the curve generator
    ECPoint generator = curve.getG();
    BigInteger x = generator.getXCoord().toBigInteger();
    BigInteger y = generator.getYCoord().toBigInteger();
    checkEquals(x, curveGeneratorX, "checkCurve");
    checkEquals(y, curveGeneratorY, "checkCurve");
    BigInteger a = curve.getCurve().getA().toBigInteger();
    BigInteger b = curve.getCurve().getB().toBigInteger();
    // Y^2 = X^3 + 7 , so a = 0 and b = 7
    checkEquals(a, BigInteger.ZERO, "checkCurve");
    checkEquals(b, BigInteger.valueOf(7), "checkCurve");
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
    checkCondition(isKeyFromSecret1(key), "checkFromPrivateFromBigInteger");
    checkCondition(key.isCompressed(), "checkFromPrivateFromBigInteger");
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
    checkCondition(time <= current, "checkGetCreationTimeSeconds");
    // should not be more than one second apart
    checkCondition(Math.abs(time - current) < 1, "checkGetCreationTimeSeconds");
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

}

