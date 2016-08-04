import java.util.Comparator;
import java.util.Date;
import java.math.BigInteger;
import java.lang.Math;
import java.security.SecureRandom;

import org.bitcoinj.core.ECKey;
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
    checkPubkeyComparator();
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
  }


  // used to initialize private field
  private BigInteger getCurveOrder(){
    String str1 = "FFFFFFFF";
    String str2 = "FFFFFFFE";
    String str3 = "BAAEDCE6"; 
    String str4 = "AF48A03B";
    String str5 = "BFD25E8C"; 
    String str6 = "D0364141";
    String str = str1 + str1 + str1 + str2 + str3 + str4 + str5 + str6;
    return new BigInteger(str, 16);
  }

  // used to initialize private field
  private BigInteger getCurveGeneratorX(){
    String str1 = "79BE667E"; 
    String str2 = "F9DCBBAC"; 
    String str3 = "55A06295"; 
    String str4 = "CE870B07"; 
    String str5 = "029BFCDB"; 
    String str6 = "2DCE28D9";
    String str7 = "59F2815B"; 
    String str8 = "16F81798";
    String str = str1 + str2 + str3 + str4 + str5 + str6 + str7 + str8;
    return new BigInteger(str, 16);
  }

  // used to initialize private field
  private BigInteger getCurveGeneratorY(){
    String str1 = "483ADA77"; 
    String str2 = "26A3C465"; 
    String str3 = "5DA4FBFC"; 
    String str4 = "0E1108A8"; 
    String str5 = "FD17B448"; 
    String str6 = "A6855419";
    String str7 = "9C47D08F"; 
    String str8 = "FB10D4B8";
    String str = str1 + str2 + str3 + str4 + str5 + str6 + str7 + str8;
    return new BigInteger(str, 16);
  }

  // private key example from 'Mastering bitcoin'
  private BigInteger getSecret1(){
    String str1 = "1E99423A";
    String str2 = "4ED27608";
    String str3 = "A15A2616";
    String str4 = "A2B0E9E5";
    String str5 = "2CED330A";
    String str6 = "C530EDCC";
    String str7 = "32C8FFC6";
    String str8 = "A526AEDD";
    String str = str1 + str2 + str3 + str4 + str5 + str6 + str7 + str8;
    return new BigInteger(str, 16);
  }


  private boolean isKeyFromSecret1(ECKey key){

    if (key.getPrivKey() != secret1) return false;
    // TODO possibly other validations here

    return true;
  }


  // data derived from independent sources
  private final BigInteger curveOrder = getCurveOrder();
  private final BigInteger halfCurveOrder = curveOrder.shiftRight(1); // div 2
  private final BigInteger curveGeneratorX = getCurveGeneratorX();
  private final BigInteger curveGeneratorY = getCurveGeneratorY();
  private final BigInteger secret1 = getSecret1();



  // used for validating various methods and property
  private final ECKey key1 = ECKey.fromPrivate(secret1);


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
  public void checkPubkeyComparator(){
    Comparator<ECKey> comp = ECKey.PUBKEY_COMPARATOR;
  }

  public void checkConstructorDefault(){
    ECKey key = new ECKey();  // generate new keypair
    checkNotNull(key, "checkConstructorDefault");
  }

  public void checkConstructorFromSecureRandom(){
    SecureRandom random = new SecureRandom();  
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


}

