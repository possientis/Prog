import java.util.Comparator;
import java.util.Date;
import java.util.Arrays;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.lang.Math;
import javax.xml.bind.DatatypeConverter;
import java.security.SecureRandom;

import org.bitcoin.Secp256k1Context;
import org.bitcoin.NativeSecp256k1;
import org.bitcoin.NativeSecp256k1Util;

import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.DumpedPrivateKey;
import org.bitcoinj.core.Address;
import org.bitcoinj.wallet.Protos.Wallet.EncryptionType;
import org.bitcoinj.crypto.LazyECPoint;
import org.bitcoinj.crypto.KeyCrypter;
import org.bitcoinj.crypto.KeyCrypterScrypt;
import org.bitcoinj.crypto.EncryptedData;


import org.spongycastle.crypto.params.ECDomainParameters;
import org.spongycastle.crypto.params.KeyParameter;
import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;
import org.spongycastle.crypto.digests.RIPEMD160Digest;
import org.spongycastle.crypto.digests.SHA256Digest;
import org.spongycastle.crypto.signers.HMacDSAKCalculator;
import org.spongycastle.crypto.signers.ECDSASigner;
import org.spongycastle.crypto.params.ECPrivateKeyParameters;
import org.spongycastle.crypto.ec.CustomNamedCurves;
import org.spongycastle.asn1.DERSequenceGenerator;
import org.spongycastle.asn1.ASN1Integer;
import org.spongycastle.asn1.DEROctetString;
import org.spongycastle.asn1.x9.X9ECParameters;
import org.spongycastle.asn1.ASN1Primitive;
import org.spongycastle.asn1.DERTaggedObject;
import org.spongycastle.asn1.DERBitString;

import com.google.common.primitives.UnsignedBytes;


public class Test_ECKey extends Test_Abstract {

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

  private static String _getFieldPrimeAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
  }

  private static BigInteger _getFieldPrime(){
    return new BigInteger(_getFieldPrimeAsHex(), 16);
  }

  private static String _getCurveOrderAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"; 
  }

  private static BigInteger _getCurveOrder(){
    return new BigInteger(_getCurveOrderAsHex(), 16);
  }

  private static String _getCurveGeneratorXAsHex(){
    return "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"; 
  }

  private static BigInteger _getCurveGeneratorX(){
    return new BigInteger(_getCurveGeneratorXAsHex(), 16);
  }

  private static String _getCurveGeneratorYAsHex(){
    return "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";
  }

  // used to initialize private field
  private static BigInteger _getCurveGeneratorY(){
    return new BigInteger(_getCurveGeneratorYAsHex(), 16);
  }

  // private key example from 'Mastering bitcoin'
  private static String _getSecret1AsHex(){
    return "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";
  }
    
  private static BigInteger _getSecret1(){
    return new BigInteger(_getSecret1AsHex(), 16);
  }

  private static String _getSecret1AsWiF(){
    // 0x80 | private key | 0x01 | checksum
    // This is main net so version byte is 0x80 = 128
    // This is a compressed key of single byte suffix 0x01 added
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j 1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD 
    return "KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ";
    //      KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ
  }

  private static String _getSecret1AsWiFUncomp(){
    // 0x80 | private key | checksum
    // This is main net so version byte is 0x80 = 128
    // This is an uncompressed key so no single 0x01 suffix byte
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j 1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD 
    return "5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn";
    //      5J3mBbAH58CpQ3Y5RNJpUKPE62SQ5tfcvU2JpbnkeyhfsYB1Jcn
  }


  private static String _getSecret1AsWiFTest(){
    // 0xEF | private key | 0x01 | checksum
    // This is a test network so version byte is 0xEF = 239
    // This is a compressed key so single byte suffix 0x01 added
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j -n XTN 1E99423A4ED27608A15A2616A2B0E9E52CED33...C8FFC6A526AEDD 
    return "cNcBUemoNGVRN9fRtxrmtteAPQeWZ399d2REmX1TBjvWpRfNMy91";
    //      cNcBUemoNGVRN9fRtxrmtteAPQeWZ399d2REmX1TBjvWpRfNMy91
  }

  private static String _getSecret1AsWiFTestUncomp(){
    // 0xEF | private key | checksum
    // This is a test network so version byte is 0xEF = 239
    // This is an uncompressed key so no single 0x01 suffix byte
    // 4 bytes checksum
    // This string can be retrieved using libbitcoin or pycoin 
    // ku -j -n XTN 1E99423A4ED27608A15A2616A2B0E9E52CED33...C8FFC6A526AEDD 
    return "91pPmKypfMGxN73N3iCjLuwBjgo7F4CpGQtFuE9FziSieVTY4jn";
    //      91pPmKypfMGxN73N3iCjLuwBjgo7F4CpGQtFuE9FziSieVTY4jn
  }


  private static byte[] _getSecret1AsBytes(){
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
  private static String _getSecret1PubKeyXAsHex(){
    return "F028892BAD7ED57D2FB57BF33081D5CFCF6F9ED3D3D7F159C2E2FFF579DC341A";
  }

  private static BigInteger _getSecret1PubKeyX(){
    return new BigInteger(_getSecret1PubKeyXAsHex(), 16);
  }


  // obtained from independent source
  private static String _getSecret1PubKeyYAsHex(){
    // leading zero matters here, as we append strings together
    return "07CF33DA18BD734C600B96A72BBC4749D5141C90EC8AC328AE52DDFE2E505BDB";
  }


  private static BigInteger _getSecret1PubKeyY(){
    return new BigInteger(_getSecret1PubKeyYAsHex(), 16);
  }

  private static String _getSecret1PubKeyAsHex(){
    return "03" + _getSecret1PubKeyXAsHex();
  }

  private static BigInteger _getSecret1PubKey(){
    return new BigInteger(_getSecret1PubKeyAsHex(), 16);
  }

  private static String _getSecret1PubKeyUncompAsHex(){
    return "04" + _getSecret1PubKeyXAsHex() + _getSecret1PubKeyYAsHex();
  }


  private static BigInteger _getSecret1PubKeyUncomp(){
    return new BigInteger(_getSecret1PubKeyUncompAsHex(), 16);
  }

  private static String _getSecret1PubKeyHashAsHex(){
    return "BBC1E42A39D05A4CC61752D6963B7F69D09BB27B";
  }

  private static BigInteger _getSecret1PubKeyHash(){
    return new BigInteger(_getSecret1PubKeyHashAsHex(), 16);
  }


  private static String _getSecret1PubKeyHashUncompAsHex(){
    return "211B74CA4686F81EFDA5641767FC84EF16DAFE0B";
  }

  private static BigInteger _getSecret1PubKeyHashUncomp(){
    return new BigInteger(_getSecret1PubKeyHashUncompAsHex(), 16);
  }

  private static String _getSecret1Address(){
    return "1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy";
  }

  private static String _getSecret1AddressUncomp(){
    return "1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x";
  }

  private static NetworkParameters _getMainNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_MAINNET);
  }

  private static NetworkParameters _getRegTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_REGTEST);
  }

  private static NetworkParameters _getTestNetNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_TESTNET);
  }

  private static NetworkParameters _getUnitTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_UNITTESTNET);
  }

  private static final BigInteger 
    fieldPrime = _getFieldPrime();
  private static final BigInteger 
    _curveOrder = _getCurveOrder();
  private static final BigInteger 
    halfCurveOrder = _curveOrder.shiftRight(1);
  private static final BigInteger 
    curveGeneratorX = _getCurveGeneratorX();
  private static final BigInteger 
    curveGeneratorY = _getCurveGeneratorY();
  private static final String 
    _curveOrderAsHex = _getCurveOrderAsHex();
  private static final X9ECParameters 
    curX9 = CustomNamedCurves.getByName("secp256k1"); 
  private static final ASN1Primitive 
    curASN1 = curX9.toASN1Primitive();

  // key from Mastering Bitcoin
  private static final BigInteger 
    secret1 = _getSecret1();
  private static final BigInteger 
    secret1PubKeyX = _getSecret1PubKeyX();
  private static final BigInteger 
    secret1PubKeyY = _getSecret1PubKeyY();
  private static final BigInteger 
    secret1PubKey = _getSecret1PubKey();
  private static final BigInteger 
    secret1PubKeyUncomp = _getSecret1PubKeyUncomp();
  private static final BigInteger 
    secret1PubKeyHash = _getSecret1PubKeyHash();
  private static final BigInteger 
    secret1PubKeyHashUncomp = _getSecret1PubKeyHashUncomp();
  
  private static final String 
    secret1AsHex = _getSecret1AsHex();
  private static final String 
    secret1AsWiF = _getSecret1AsWiF();
  private static final String 
    secret1AsWiFUncomp = _getSecret1AsWiFUncomp();
  private static final String 
    secret1AsWiFTest = _getSecret1AsWiFTest();
  private static final String 
    secret1AsWiFTestUncomp = _getSecret1AsWiFTestUncomp();
  private static final String 
    secret1PubKeyXAsHex = _getSecret1PubKeyXAsHex();
  private static final String 
    secret1PubKeyYAsHex = _getSecret1PubKeyYAsHex();
  private static final String 
    secret1PubKeyAsHex = _getSecret1PubKeyAsHex();
  private static final String 
    secret1PubKeyUncompAsHex = _getSecret1PubKeyUncompAsHex();
  private static final String 
    secret1Address = _getSecret1Address();
  private static final String 
    secret1AddressUncomp = _getSecret1AddressUncomp();

  private static final byte[] 
    secret1AsBytes = _getSecret1AsBytes();

  private static final ECKey 
    key1 = ECKey.fromPrivate(secret1);
  private static final ECKey 
    key1Uncomp = ECKey.fromPrivate(secret1, false);

  // other data
  private static final NetworkParameters mainNet = _getMainNetwork();
  private static final NetworkParameters regTestNet = _getRegTestNetwork();
  private static final NetworkParameters testNetNet = _getTestNetNetwork();
  private static final NetworkParameters unitTestNet = _getUnitTestNetwork();

  private static BigInteger _getRandomSecret(){
    byte[] bytes;
    boolean isGood = false;
    BigInteger secret = BigInteger.ZERO;

    while(!isGood)
    {
      bytes = getRandomBytes(32);
      secret = new BigInteger(1, bytes);  // unsigned
      // we want secret to satisfy 1 < secret < _curveOrder
      if(secret.compareTo(BigInteger.ONE)>0 && secret.compareTo(_curveOrder)<0)
      {
        isGood = true;
      }
    }

    return secret;
  }

  private static boolean _isKeyFromSecret1(ECKey key){
    if (!key.getPrivKey().equals(secret1)) return false;
    return true;
  }

  private static BigInteger _sqrt(BigInteger n, boolean isEven){
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
    checkEquals(n1.multiply(n1).mod(p), arg, "_sqrt.1");
    checkEquals(n2.multiply(n2).mod(p), arg, "_sqrt.2");

    // retrieving parity of each square root
    boolean isEven1 = (n1.mod(two) == BigInteger.ZERO);
    boolean isEven2 = (n2.mod(two) == BigInteger.ZERO);

    // if one is even, the other should be odd
    checkCondition((isEven1 && !isEven2) || (!isEven1 && isEven2), "_sqrt.3");

    return isEven ? (isEven1 ? n1 : n2) : (isEven1 ? n2 : n1);
  }

  private static BigInteger _YFromX(BigInteger x, boolean isEven){
    // returns Y such that Y^2 = X^3 + 7 modulo p of given parity
    BigInteger p = fieldPrime;
    BigInteger seven = BigInteger.valueOf(7);
    BigInteger square = x.multiply(x).mod(p);
    BigInteger cube = square.multiply(x).mod(p);
    BigInteger sum = cube.add(seven);
    return _sqrt(sum, isEven);
  }

  private static boolean _isEven(BigInteger y){
    BigInteger p = fieldPrime;
    BigInteger two = BigInteger.ONE.shiftLeft(1);
    BigInteger arg = y.mod(p);
    return (arg.mod(two) == BigInteger.ZERO);
  }
  
  private static String _toString(ECKey key){
    StringBuilder builder = new StringBuilder("ECKey{pub HEX="); 
    builder.append(key.getPublicKeyAsHex());
    builder.append(", isEncrypted=");
    builder.append(key.isEncrypted());
    builder.append(", isPubKeyOnly=");
    builder.append(key.isPubKeyOnly());
    builder.append("}");
    return builder.toString();
  }
  
  private static String _toStringWithPrivate(
      ECKey key, 
      NetworkParameters params)
  {
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

  private static String _formatKey(
      ECKey key, 
      boolean priv, 
      NetworkParameters params)
  {
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


  private static byte[] _ripemd160(byte[] input){
    // we are not supposed to call this on inputs other
    // than 32 bytes long. Hence this restriction for safety
    checkEquals(32, input.length, "_ripemd160.1");
    byte[] out = new byte[20];
    RIPEMD160Digest digest = new RIPEMD160Digest();
    digest.update(input, 0, input.length);  
    digest.doFinal(out, 0);
    return out;
  }


  // returns the sum point + point with respect to the
  // secp256k1 elliptic curve addition. This is implemented
  // in order to validate the getPubKeyPoint method 
  private static ECPoint _twice(ECPoint point){

    ECCurve curve = point.getCurve();

    // should not use this function outside of secp256k1 scope
    String name = "org.spongycastle.math.ec.custom.sec.SecP256K1Curve"; 
    checkCondition(curve.getClass().getName() == name, "_twice.1");

    // point should be normalized
    checkCondition(point.isNormalized(), "_twice.2");
     
    // case 1: point is infinity
    if (point.isInfinity()) return curve.getInfinity(); 
    
    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();
    BigInteger p = fieldPrime;

    // expeciting 0 <= x < p and 0 <= y < p
    checkCondition(BigInteger.ZERO.compareTo(x) <= 0, "_twice.3");
    checkCondition(x.compareTo(p) < 0, "_twice.4");
    checkCondition(BigInteger.ZERO.compareTo(y) <= 0, "_twice.5");
    checkCondition(y.compareTo(p) < 0, "_twice.6");

    // case 2: 2y = 0 (which is equivalent to y = 0 in Fp, p odd prime)
    // The point is of the form (x,0), and the tangent to the EC curve
    // at that point is vertical, so (x,0) + (x,0) is the infinity point
    if(y == BigInteger.ZERO) return curve.getInfinity();

    // case 3: 2y <> 0
    // (x,y) + (x,y) = (X,-Y) where 
    // X = lambda^2 - 2x
    // Y = lambda.X + nu
    // nu = y - lambda.x
    // lambda = (3.x^2 + a)/(2y) with a = 0 for secp256k1.

    // lambda
    BigInteger square_x = x.multiply(x).mod(p); 
    BigInteger twice_square_x = square_x.shiftLeft(1).mod(p);
    BigInteger three_square_x = twice_square_x.add(square_x).mod(p); 
    BigInteger twice_y = y.shiftLeft(1).mod(p);
    BigInteger one_over_twice_y = twice_y.modInverse(p);
    BigInteger lambda = three_square_x.multiply(one_over_twice_y).mod(p);
    
    // nu
    BigInteger lambda_x = lambda.multiply(x).mod(p);
    BigInteger nu = y.subtract(lambda_x).mod(p);

    // X
    BigInteger lambda_square = lambda.multiply(lambda).mod(p);
    BigInteger twice_x = x.shiftLeft(1).mod(p);
    BigInteger X = lambda_square.subtract(twice_x).mod(p);

    // Y
    BigInteger lambda_X = lambda.multiply(X).mod(p);
    BigInteger Y = lambda_X.add(nu).mod(p);


    // returning point
    return curve.createPoint(X, Y.negate().mod(p));
  }

  // returns the sum p1 + p2 with respect to the secp256k1 
  // elliptic curve addition. This is implemented
  // in order to validate the getPubKeyPoint method 
  private static ECPoint _add(ECPoint p1, ECPoint p2){
    ECCurve curve = p1.getCurve();

    // both point should be with respect to the same elliptiic curve
    checkEquals(curve, p2.getCurve(), "_add.1");

    // should not use this function outside of secp256k1 scope
    String name = "org.spongycastle.math.ec.custom.sec.SecP256K1Curve"; 
    checkCondition(curve.getClass().getName() == name, "_add.2");

    // point should be normalized
    checkCondition(p1.isNormalized(), "_add.3");
    checkCondition(p2.isNormalized(), "_add.4");

    // case 1: p1 and p2 are equal
    if(p1.equals(p2)) return _twice(p1);

    // case 2: p1 and p2 are diferent points
    // case 2.a: p1 is infinity
    if(p1.isInfinity()){
      // returning copy of p2
      BigInteger x = p2.getAffineXCoord().toBigInteger();
      BigInteger y = p2.getAffineYCoord().toBigInteger();
      return curve.createPoint(x,y);
    }

   // case 2.b: p2 is infinity
   if(p2.isInfinity()){
      // returning copy of p1
      BigInteger x = p1.getAffineXCoord().toBigInteger();
      BigInteger y = p1.getAffineYCoord().toBigInteger();
      return curve.createPoint(x,y);
    }


   // None of p1 and p2 are infinity at this stage
   // so p1 = (x1,y1) and p2=(x2,y2)

   BigInteger p = fieldPrime;
   BigInteger x1 = p1.getAffineXCoord().toBigInteger().mod(p);
   BigInteger y1 = p1.getAffineYCoord().toBigInteger().mod(p);
   BigInteger x2 = p2.getAffineXCoord().toBigInteger().mod(p);
   BigInteger y2 = p2.getAffineYCoord().toBigInteger().mod(p);

   // case 2.c: x1 = x2, the line going through p1 and p2 is vertical
   // p1 + p2 is therefore the infinity point
   if(x1.equals(x2)) return curve.getInfinity(); 


   // case 2.d: x1 <> x2
   // p1 + p2 is (X, -Y) where:
   // X = lambda^2 - x1 -x2
   // Y = lambda.X + nu
   // nu = y1 - lambda.x1
   // lambda = (y2 - y1)/(x2 - x1)


   // lambda
   BigInteger diff_y = y2.subtract(y1).mod(p);
   BigInteger diff_x = x2.subtract(x1).mod(p);
   BigInteger one_over_diff_x = diff_x.modInverse(p);
   BigInteger lambda = diff_y.multiply(one_over_diff_x).mod(p);

   // nu
   BigInteger lambda_x1 = lambda.multiply(x1).mod(p);
   BigInteger nu = y1.subtract(lambda_x1).mod(p);

   // X
   BigInteger lambda_square = lambda.multiply(lambda).mod(p);
   BigInteger sum_x1_x2 = x1.add(x2).mod(p); 
   BigInteger X = lambda_square.subtract(sum_x1_x2).mod(p);

   // Y
   BigInteger lambda_X = lambda.multiply(X).mod(p);
   BigInteger Y = lambda_X.add(nu).mod(p);

   
    // returning point
    return curve.createPoint(X, Y.negate().mod(p)); 
  }

  // function implemented for the purpose of validating getPubKeyPoint
  private static ECPoint _getPubKeyPoint(ECKey key){
    BigInteger secret = key.getPrivKey();
    ECCurve curve = ECKey.CURVE.getCurve();
    // generator of the secp256k1 elliptic curve group
    ECPoint g = curve.createPoint(curveGeneratorX, curveGeneratorY);

    // Setting up result
    ECPoint result = curve.getInfinity(); // the identity of the EC group
    ECPoint G = g;  // successively equal to g, 2g, 4g, 8g, ...,  (2^256)g
    for(int i = 0; i < 256; ++i){
      if(secret.testBit(0)){
        result = _add(result, G);
      }
      G = _twice(G);
      secret = secret.shiftRight(1);
    }

    return result;
  }

  private static ECKey _getNewEncryptedKey(String passphrase){
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey(passphrase);
    ECKey k1 = new ECKey(); // unencrypted
    ECKey k2 = k1.encrypt(crypter, aesKey);
    return k2;
  }

  private static ECKey.ECDSASignature _signNative(
      Sha256Hash input, 
      byte[] priv)
  {

    // being ultra careful before calling native C
    checkCondition(Secp256k1Context.isEnabled(), "_signNative.1");
    checkNotNull(input, "_signNative.2");
    checkNotNull(priv, "_signNative.3");
    checkEquals(priv.length, 32, "_signNative.4");

    try {
      byte[] signature = NativeSecp256k1.sign(input.getBytes(), priv);
      return ECKey.ECDSASignature.decodeFromDER(signature);
    } catch (NativeSecp256k1Util.AssertFailException e){
      checkCondition(false, "_signNative.5");
      return null;
    }
  }

  private static ECKey.ECDSASignature _signSpongy(
      Sha256Hash input, 
      byte[] priv)
  {

    SHA256Digest digest = new SHA256Digest();
    HMacDSAKCalculator calculator = new HMacDSAKCalculator(digest);
    ECDSASigner signer = new ECDSASigner(calculator);

    BigInteger secret = new BigInteger(1, priv);
    ECPrivateKeyParameters key = new ECPrivateKeyParameters(secret, ECKey.CURVE);

    signer.init(true, key);
    BigInteger[] components = signer.generateSignature(input.getBytes());

    BigInteger r = components[0];
    BigInteger s = components[1];

    return new ECKey.ECDSASignature(r,s).toCanonicalised();
  }

  private static BigInteger _getDeterministicKey(
      BigInteger secret,
      Sha256Hash message,
      int index)
  {
    // ECDSA Signature scheme requires the generation of a random private key
    // However, using the same random private key twice to sign two different
    // messages exposes the signer's private key with potentially disastrous
    // consequences for someone re-using the same bitcoin address. To avoid 
    // this risk, a pseudo-random private key is generated from the signer's 
    // private key and message. An index argument exists to allow the retrieval
    // of various elements of the pseudo-random sequence. In practice, calling
    // the function with index = 0 should be enough, but it is possible to use
    // index = 1, 2 , .. in the unlikely event that a fresh key is required.
    
    checkCondition(index >= 0, "_getDeterministicKey.1");

    BigInteger q = ECKey.CURVE.getN();  // secp256k1 curve order

    SHA256Digest digest = new SHA256Digest();

    HMacDSAKCalculator calculator = new HMacDSAKCalculator(digest);

    calculator.init(q, secret, message.getBytes());

    int count = 0;

    BigInteger k = null;

    while(count <= index)
    {
      k = calculator.nextK(); 

      ++count;
    }

    // returned k should be integer modulo q. Checking just in case

    checkCondition(k.compareTo(BigInteger.ZERO) >= 0, "_getDeterministicKey.2");

    checkCondition(k.compareTo(q) < 0, "_getDeterministicKey.3");

    return k;
  }

  private static BigInteger _getProjection(ECPoint point)
  {
    // when using the DSA or ECDSA signature scheme, we typically have 
    // an underlying cyclic group G and some mapping proj: G -> Fq which 
    // projects the group elements to the prime field Fq modulo the order 
    // of the group. This projection mapping is required when computing 
    // a signature (r,s), as r = proj(kG') where k is some random or pseudo
    // -random non-zero element of Fq, and G' is the chosen generator of 
    // the cyclic group. In the case of DSA, the group is a cyclic subgroup 
    // (of prime order q) of Zp* for some prime p (so q divides p - 1), 
    // and proj: G -> Fq simply sends [x]p (class modulo p) to [x]q (class 
    // modulo q), where the representative x of [x]p is chosen in [0,p-1]. 
    // In the case of ECDSA, the group is an elliptic curve and a point 
    // ([x]p,[y]p) is sent to [x]q.

    if(point.isInfinity()) return BigInteger.ZERO;  // projection always defined

    BigInteger p = fieldPrime;

    BigInteger q = ECKey.CURVE.getN();  // seckp256k1 curve order

    BigInteger x = point.getAffineXCoord().toBigInteger();

    // asserting that 0 <= x < p
 
    checkCondition(BigInteger.ZERO.compareTo(x) <= 0, "_getProjection.1");

    checkCondition(x.compareTo(p) == -1, "_getProjection.2");
    
    return x.mod(q);
  }

  private static BigInteger _getProjection(Sha256Hash hash)
  {
    // just like in the case of an ECPoint, a message hash needs to 
    // be projected onto the prime field Fq (where q is the curve order)
    // in order to produce a signature. The projection mapping
    // proj : Hash -> Fq is simply a reduction modulo q
    
    BigInteger q = ECKey.CURVE.getN();

    return hash.toBigInteger().mod(q);
  }


  private static ECKey.ECDSASignature _signCheck(
      Sha256Hash  message, 
      byte[]      priv)
  {
    
    BigInteger q = ECKey.CURVE.getN();  // order of secp256k1

    BigInteger x = new BigInteger(1, priv).mod(q); // signer's private key

    boolean newKeyNeeded = true;        // will loop until false

    int index = 0;                      // index in pseudo-radom sequence

    BigInteger r = null;                // returning (r,s)

    BigInteger s = null;                // returning (r,s)


    while(newKeyNeeded)
    {

      // First obtain deterministic pseudo random secret k
      BigInteger k = _getDeterministicKey(x, message, index++);

      if(k.equals(BigInteger.ZERO)) continue; // start all over

      // get associated ECPoint
      ECPoint point = ECKey.publicPointFromPrivate(k).normalize();

      // signature = (r,s)
      r = _getProjection(point);

      if(r.equals(BigInteger.ZERO)) continue; // start all over

      // message hash needs to be projected onto prime field Fq 
      BigInteger e = _getProjection(message);

      // signature = (r,s) where s = k^(-1)(e + rx)
      // This latter expression is an algebraic expression in the field Fq 

      s = r.multiply(x).mod(q);               // s = rx
      s = e.add(s).mod(q);                    // s = e + rx
      s = k.modInverse(q).multiply(s).mod(q); // s = k^(-1)(e + rx)

      if(s.equals(BigInteger.ZERO)) continue; // start all over

      newKeyNeeded = false;

    }

    return new ECKey.ECDSASignature(r,s).toCanonicalised();
  }

  private static ECKey _recoverFromSignature(
  // Attempting to replicate the functionality of ECKey's method.
      int                   recoveryId, 
      ECKey.ECDSASignature  signature,
      Sha256Hash            message,
      boolean               compressed)
  {
    // Returns the public key associated with an ECDSA signature
    // given the message. A compressed argument is needed to decide
    // whether the returned key should be in compressed format
    //
    // Strictly speaking an ECDSA signature does not allow the recovery
    // of the underlying public key, as there are potentially 4 public 
    // keys (sometimes only 2) which are possible candidates. Hence,
    // an additional argument 'recoveryId' of 2 bits information is
    // needed to decide which of the potential 4 candidates should be
    // returned. More explanation follows now: 
    //
    // Recall that an ECDSA signature is an ordered pair (r,s) of non-zero
    // elements of the prime field Fq, where q is the order of secp256k1.
    // Given the message hash and its projection e on Fq, a signature (r,s)
    // is valid with respect to the public key X if and only if the ECPoint
    // (s^(-1)e)G + (s^(-1)r)X when projected onto Fq yields r itself, i.e.
    //
    // proj[ (s^(-1)e)G + (s^(-1)r)X ] == r
    //
    // where G is the generator of the elliptic curve secp256k1. For each
    // ECPoint Y satisfying the equation proj[Y] == r, we can therefore
    // derive a public key X for which the signature (r, s) is valid, given e.
    //
    // X = (r^(-1)s)Y - (r^(-1)e)G
    // 
    // Note that distinct values of Y lead to distinct values of X, so there
    // are as many validating keys as there are solutions to the equation
    // proj[Y] == r. Now in order to solve this equation, we can first note
    // that any potential solution Y can be written as Y = (a,b) where a , b
    // are integers (modulo p), so we may assume that 0 <= a < p and 0 <= b < p,
    // where p is the prime characteritic of the field Fp underlying the curve.
    // With these notations, we have proj[Y] = a mod q and the equation can
    // therefore be equivalently expressed as a mod q == r. Since q < p, r 
    // also satisfies the inequalities 0 <= r < p and an obvious solution
    // is a = r, which yields two points Y = (a,b) (one for each parity of b).
    // However, if r happens to be small enough so that r + q < p, then 
    // a = r + q will also be a solution of a mod q == r, yielding a further 
    // two points Y = (a, b). We are now in a position to interpret the 2 bits 
    // argument recoverId: the highest order bit determines whether we are
    // returning a public key corresponding to a = r (bit = 0), or a = r + q
    // (bit = 1), being understood that in the latter case a public key can
    // only be returned if r + q < p (the function should return null otherwise).
    // The lowest order bit determines the parity of b (even = 0, odd = 1). 




    return null;
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
    checkEquals(curve.getN(), _curveOrder, "checkCurve.2");
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

    // checking order of elliptic group and underlying field prime
    checkCondition(prime.isProbablePrime(128), "checkCurve.9");
    checkCondition(_curveOrder.isProbablePrime(128), "checkCurve.10");
    ECPoint check = ECKey.publicPointFromPrivate(_curveOrder);
    // (_curveOrder) x G = infinity. This shows that the order of the 
    // point G divides _curveOrder. However, _curveOrder is prime, and
    // G is not infinity (its order is not 1). It follows that the
    // order of G is _curveOrder. This does not actually prove that
    // _curveOrder is indeed the order of the group. 
    checkCondition(check.isInfinity(), "checkCurve.11");
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
    ECKey k1 = new ECKey();
    ECKey k2 = new ECKey();
    checkEquals(
        comp1.compare(k1,k2),
        comp2.compare(k1.getPubKey(), k2.getPubKey()),
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
    SecureRandom random = new SecureRandom();
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
    ECKey k1 = new ECKey();
    checkCondition(k1.isCompressed(),"checkDecompress.1");
    ECKey k2 = k1.decompress();
    checkCondition(!k2.isCompressed(),"checkDecompress.2");
    checkEquals(k1.getPrivKey(), k2.getPrivKey(), "checkDecompress.3");
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
    KeyParameter aesKey1 = crypter1.deriveKey("some arbitrary passphrase");
    ECKey k1 = new ECKey();
    ECKey k2 = k1.encrypt(crypter1, aesKey1); 
    // so we have an encrypted k2
    KeyCrypter crypter2 = k2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some arbitrary passphrase"); 
    ECKey k3 = k2.decrypt(aesKey2);
    checkEquals(k1.getPrivKey(), k3.getPrivKey(), "checkDecrypt.1");
  }

  public void checkDecryptFromKeyCrypter(){
    KeyCrypter crypter1 = new KeyCrypterScrypt();
    KeyParameter aesKey1 = crypter1.deriveKey("some arbitrary passphrase");
    ECKey k1 = new ECKey();
    ECKey k2 = k1.encrypt(crypter1, aesKey1); 
    // so we have an encrypted k2
    KeyCrypter crypter2 = k2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some arbitrary passphrase"); 
    ECKey k3 = k2.decrypt(crypter2, aesKey2);
    checkEquals(
        k1.getPrivKey(), 
        k3.getPrivKey(), 
        "checkDecryptFromKeyCrypter.1"
    );
  }

  public void checkEncrypt(){
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
    ECKey k1 = new ECKey();
    ECKey k2 = k1.encrypt(crypter, aesKey); 
    checkCondition(k2.isEncrypted(),"checkEncrypt.1");
    checkCondition(k2.isPubKeyOnly(),"checkEncrypt.2");
    checkCondition(!k2.isWatching(),"checkEncrypt.3");
    BigInteger n1 = new BigInteger(1, k1.getPubKey()); 
    BigInteger n2 = new BigInteger(1, k2.getPubKey()); 
    // unencrypted and encrypted key should have the same public key
    checkEquals(n1, n2, "checkEncrypt.4");
  }

  public void checkEncryptionIsReversible(){
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
    ECKey k1 = new ECKey();
    ECKey k2 = k1.encrypt(crypter, aesKey); 
    checkCondition(
        ECKey.encryptionIsReversible(k1, k2, crypter, aesKey),
        "checkEncryptionIsReversible.1"
    );
    /* this create warning in the log, dunno how to suppress it
    KeyParameter aesWrongKey = crypter.deriveKey("This passphrase is wrong");
    checkCondition(
        !ECKey.encryptionIsReversible(k1, k2, crypter, aesWrongKey),
        "checkEncryptionIsReversible.2"
    );
    */
  }

  public void checkECKeyEquals(){
    // equals and hashCode are inconsistent
    logMessage("-> ECKey::equals see unit testing code ...");
    ECKey k1 = new ECKey();
    ECKey k2 = ECKey.fromPrivate(k1.getPrivKey());
    checkCondition(!k1.equals(k2), "checkHashCode.1");
    checkEquals(k1.hashCode(), k2.hashCode(), "checkHashCode.2");
 
    // naive testing in the meantime
    k2 = new ECKey();
    checkCondition(k1.equals(k1),"checkECKeyEquals.1");
    checkCondition(k2.equals(k2),"checkECKeyEquals.2");
    checkCondition(!k1.equals(k2),"checkECKeyEquals.3");
    checkCondition(!k2.equals(k1),"checkECKeyEquals.3");
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
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
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
    checkCondition(_isKeyFromSecret1(key), "checkFromPrivateFromBigInteger.1");
    checkCondition(key.isCompressed(), "checkFromPrivateFromBigInteger.2");
  }

  public void checkFromPrivateFromBigIntegerBool(){
    // compressed
    ECKey key = ECKey.fromPrivate(secret1, true); // compressed = true 
    checkCondition(_isKeyFromSecret1(key), "checkFromPrivateFromBigIntegerBool.1");
    checkCondition(key.isCompressed(), "checkFromPrivateFromBigIntegerBool.2");
    // uncompressed
    key = ECKey.fromPrivate(secret1, false);      // compressed = false
    checkCondition(_isKeyFromSecret1(key), "checkFromPrivateFromBigIntegerBool.3");
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
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
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
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
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
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);
    checkCondition(
        k2.getEncryptionType() == EncryptionType.ENCRYPTED_SCRYPT_AES,
        "checkGetEncryptionType.2"
    );
  }

  public void checkGetKeyCrypter(){
    ECKey k1 = new ECKey ();
    KeyCrypter crypt1 = new KeyCrypterScrypt();
    KeyParameter aesKey = crypt1.deriveKey("some arbitrary passphrase");
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
    BigInteger secret = _getRandomSecret();
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
    BigInteger secret = _getRandomSecret();
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
      BigInteger z = _YFromX(x, isEven);
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
    for(int i = 0; i < 32; ++i){  // testing 32 times, code is slow
      ECKey key = new ECKey();
      point = key.getPubKeyPoint();
      checkCondition(point.isNormalized(), "checkGetPubKeyPoint.5");
      ECPoint check = _getPubKeyPoint(key);
      checkEquals(check, point, "checkGetPubKeyPoint.6");
    }
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
    BigInteger secret = _getRandomSecret();
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
    BigInteger secret = _getRandomSecret();
    ECKey key = ECKey.fromPrivate(secret);
    check = key.getSecretBytes();
    BigInteger n = new BigInteger(1, check); // decoding bytes back into secret
    checkEquals(secret, n, "checkGetSecretBytes.3");

  }

  public void checkHashCode(){
    // equals and hashCode are inconsistent
    // not much point validating one or the other until this is fixed

    logMessage("-> ECKey::hashCode see unit testing code ...");
    ECKey k1 = new ECKey();
    ECKey k2 = ECKey.fromPrivate(k1.getPrivKey());
    checkCondition(!k1.equals(k2), "checkHashCode.1");
    checkEquals(k1.hashCode(), k2.hashCode(), "checkHashCode.2");
  }

  public void checkHasPrivKey(){
    // key1
    checkCondition(key1.hasPrivKey(), "checkHashPrivKey.1");
    checkCondition(key1Uncomp.hasPrivKey(), "checkHashPrivKey.2");
    // random, with private key, unencrypted
    ECKey key = new ECKey();
    checkCondition(key.hasPrivKey(), "checkHashPrivKey.3");
    // random, with private key, encrypted
    key = _getNewEncryptedKey("some arbitary passphrase");
    checkCondition(!key.hasPrivKey(), "checkHashPrivKey.4");
    // randon, without private key
    byte[] pubKey = key.getPubKey();
    ECKey pubOnly = ECKey.fromPublicOnly(pubKey);
    checkCondition(!pubOnly.hasPrivKey(), "checkHashPrivKey.5");
  }

  public void checkIsCompressed(){
    checkCondition(key1.isCompressed(), "checkIsCompressed.1");
    checkCondition(!key1Uncomp.isCompressed(), "checkIsCompressed.2");
    ECKey key = new ECKey();  // compressed by default
    checkCondition(key.isCompressed(), "checkIsCompressed.3");
    BigInteger secret = _getRandomSecret();
    key = ECKey.fromPrivate(secret, true);  // compressed
    checkCondition(key.isCompressed(), "checkIsCompressed.4");
    key = ECKey.fromPrivate(secret, false);  // uncompressed
    checkCondition(!key.isCompressed(), "checkIsCompressed.5");
  }

  public void checkIsEncrypted(){
    checkCondition(!key1.isEncrypted(), "checkIsEncrypted.1");
    checkCondition(!key1Uncomp.isEncrypted(), "checkIsEncrypted.2");
    // random, unencrypted
    ECKey key = new ECKey();  // not encrypted by default
    checkCondition(!key.isEncrypted(), "checkIsEncrypted.3");
    // random, encrypted
    key = _getNewEncryptedKey("some arbitrary passphrase");
    checkCondition(key.isEncrypted(), "checkIsEncrypted.4");
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
    // random, unencrypted
    ECKey key = new ECKey();
    checkCondition(!key.isPubKeyOnly(), "checkIsPubKeyOnly.3");
    // random, encryted
    key = _getNewEncryptedKey("some arbitrary passphrase");
    checkCondition(key.isPubKeyOnly(), "checkIsPubKeyOnly.4");
    // random, public only
    key = ECKey.fromPublicOnly(key.getPubKey());
    checkCondition(key.isPubKeyOnly(), "checkIsPubKeyOnly.5");
  }

  public void checkIsWatching(){
    checkCondition(!key1.isWatching(), "checkIsWatching.1");
    checkCondition(!key1Uncomp.isWatching(), "checkIsWatching.2");
    // random, unencrypted
    ECKey key = new ECKey();
    checkCondition(!key.isWatching(), "checkIsWatching.3");
    // random, encryted
    key = _getNewEncryptedKey("some arbitrary passphrase");
    checkCondition(!key.isWatching(), "checkIsWatching.4");
    // random, public only
    key = ECKey.fromPublicOnly(key.getPubKey());
    checkCondition(key.isWatching(), "checkIsPubKeyOnly.5");
  }

  public void checkMaybeDecrypt(){
    // same code as checkDecrypt.
    KeyCrypter crypter1 = new KeyCrypterScrypt();
    KeyParameter aesKey1 = crypter1.deriveKey("some arbitrary passphrase");
    ECKey k1 = new ECKey();
    ECKey k2 = k1.encrypt(crypter1, aesKey1); 
    // so we have an encrypted k2
    KeyCrypter crypter2 = k2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some arbitrary passphrase"); 
    ECKey k3 = k2.maybeDecrypt(aesKey2);
    checkEquals(k1.getPrivKey(), k3.getPrivKey(), "checkMaybeDecrypt.1");
    // will not throw on unencrypted key
    k3 = k1.maybeDecrypt(null);
    checkEquals(k1.getPrivKey(), k3.getPrivKey(), "checkMaybeDecrypt.2");
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
    BigInteger secret = _getRandomSecret();
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
    checkEquals(y1, y2, "checkPublicPointFromPrivate.3");
    // random secret
    ECKey key = new ECKey();
    BigInteger secret = key.getPrivKey();
    ECPoint p1 = ECKey.publicPointFromPrivate(secret);
    ECPoint p2 = _getPubKeyPoint(key);
    checkEquals(p1, p2, "checkPublicPointFromPrivate.4");
  }

  public void checkRecoverFromSignature(){

    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();
    byte[] priv = k1.getPrivKeyBytes(); // same for k2

    ECKey.ECDSASignature sig  = _signNative(hash, priv);
    ECKey.ECDSASignature check  = _signSpongy(hash, priv);
    checkEquals(check, sig, "checkRecoveryFromSignature.1");

    // recovering compressed public key
    ECKey temp = null;
    byte[] pub = k1.getPubKey();
    boolean found = false;
    for(int i = 0; i < 4; ++i){
      temp = ECKey.recoverFromSignature(i, sig, hash, true);
      if(temp != null){
        if(Arrays.equals(temp.getPubKey(), pub)){
          found = true;
        }
      }
    }
    checkCondition(found, "checkRecoveryFromSignature.2");

    // recovering uncompressed public key
    temp = null;
    pub = k2.getPubKey();
    found = false;
    for(int i = 0; i < 4; ++i){
      temp = ECKey.recoverFromSignature(i, sig, hash, false);
      if(temp != null){
        if(Arrays.equals(temp.getPubKey(), pub)){
          found = true;
        }
      }
    }
    checkCondition(found, "checkRecoveryFromSignature.3");
  }

  public void checkSetCreationTimeSeconds(){
    ECKey key = new ECKey();  // random, compressed
    long time1 = key.getCreationTimeSeconds() - 1000;
    key.setCreationTimeSeconds(time1);
    long time2 = key.getCreationTimeSeconds();
    checkEquals(time1, time2, "checkSetCreationTimeSeconds.1");
  }

  public void checkSign(){
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey key = new ECKey();
    byte[] priv = key.getPrivKeyBytes();
    ECKey.ECDSASignature sig = key.sign(hash);
    ECKey.ECDSASignature check1 = _signNative(hash, priv);
    ECKey.ECDSASignature check2 = _signSpongy(hash, priv);
    ECKey.ECDSASignature check3 = _signCheck(hash, priv);

    checkEquals(check1, sig, "checkSign.1");
    checkEquals(check2, sig, "checkSign.2");
    checkEquals(check3, sig, "checkSign.3");

  }

  public void checkSignFromKeyParameter(){
    Sha256Hash hash = Sha256Hash.wrap(getRandomBytes(32));
    ECKey k1 = _getNewEncryptedKey("some arbitrary passphrase");
    KeyCrypter crypter = k1.getKeyCrypter();
    KeyParameter aes = crypter.deriveKey("some arbitrary passphrase");
    ECKey.ECDSASignature sig = k1.sign(hash, aes);

    ECKey k2 = k1.decrypt(aes);
    ECKey.ECDSASignature check = k2.sign(hash);

    checkEquals(check, sig, "checkSignFromKeyParameter.1");
  }

  public void checkSignedMessageToKey(){
    ECKey k1 = new ECKey();
    String message = "This is some arbitrary message";
    Sha256Hash hash = Sha256Hash.of(message.getBytes());
    ECKey.ECDSASignature sig = k1.sign(hash);

  }

  public void checkSignMessage(){
    // TODO
  }

  public void checkSignMessageFromKeyParameter(){
    // TODO
  }

  public void checkToAddress(){
    // key1 compressed
    String scheck = key1.toAddress(mainNet).toString();
    checkEquals(scheck, secret1Address, "checkToAddress.1");

    // key1 uncompressed
    scheck = key1Uncomp.toAddress(mainNet).toString();
    checkEquals(scheck, secret1AddressUncomp, "checkToAddress.2");

    // random key
    ECKey k1 = new ECKey(); // compressed
    ECKey k2 = k1.decompress();

    Address check;

    // MainNetParams
    check = new Address(mainNet, k1.getPubKeyHash());
    checkEquals(check, k1.toAddress(mainNet), "checkToAddress.3");
    check = new Address(mainNet, k2.getPubKeyHash());
    checkEquals(check, k2.toAddress(mainNet), "checkToAddress.4");

    // RegTestParams
    check = new Address(regTestNet, k1.getPubKeyHash());
    checkEquals(check, k1.toAddress(regTestNet), "checkToAddress.5");
    check = new Address(regTestNet, k2.getPubKeyHash());
    checkEquals(check, k2.toAddress(regTestNet), "checkToAddress.6");

    // TestNet3Params
    check = new Address(testNetNet, k1.getPubKeyHash());
    checkEquals(check, k1.toAddress(testNetNet), "checkToAddress.7");
    check = new Address(testNetNet, k2.getPubKeyHash());
    checkEquals(check, k2.toAddress(testNetNet), "checkToAddress.8");

    // UnitTestParams
    check = new Address(unitTestNet, k1.getPubKeyHash());
    checkEquals(check, k1.toAddress(unitTestNet), "checkToAddress.9");
    check = new Address(unitTestNet, k2.getPubKeyHash());
    checkEquals(check, k2.toAddress(unitTestNet), "checkToAddress.10");
  }

  public void checkToASN1(){
    // key1
    byte[] bytes = key1.toASN1();
    ECKey key = ECKey.fromASN1(bytes);
    checkCondition(_isKeyFromSecret1(key), "checkToASN1.1");


    // random key
    ECKey check;
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();

    // first we check consistency with fromASN1 method
    byte[] bytes1 = k1.toASN1();
    check = ECKey.fromASN1(bytes1);
    checkEquals(check.getPrivKey(), k1.getPrivKey(), "checkToASN1.2");
    checkCondition(check.isCompressed(), "checkToASN1.3");

    byte[] bytes2 = k2.toASN1();
    check = ECKey.fromASN1(bytes2);
    checkEquals(check.getPrivKey(), k2.getPrivKey(), "checkToASN1.4");
    checkCondition(!check.isCompressed(), "checkToASN1.5");

    // We now check details of ASN1 encoding
    // replicating source code, but can't really tell if correct
    ByteArrayOutputStream baos = new ByteArrayOutputStream(400);
    // ASN1_SEQUENCE(EC_PRIVATEKEY) = {
    //   ASN1_SIMPLE(EC_PRIVATEKEY, version, LONG),
    //   ASN1_SIMPLE(EC_PRIVATEKEY, privateKey, ASN1_OCTET_STRING),
    //   ASN1_EXP_OPT(EC_PRIVATEKEY, parameters, ECPKPARAMETERS, 0),
    //   ASN1_EXP_OPT(EC_PRIVATEKEY, publicKey, ASN1_BIT_STRING, 1)
    // } ASN1_SEQUENCE_END(EC_PRIVATEKEY)
    // compressed
    try {
      DERSequenceGenerator seq = new DERSequenceGenerator(baos);
      seq.addObject(new ASN1Integer(1));  // version
      seq.addObject(new DEROctetString(k1.getPrivKeyBytes()));
      seq.addObject(new DERTaggedObject(0, curASN1)); 
      seq.addObject(new DERTaggedObject(1, new DERBitString(k1.getPubKey())));
      seq.close();
    } catch(IOException e){
      checkCondition(false, "checkToASN1.6");
    }
    checkCondition(Arrays.equals(bytes1, baos.toByteArray()), "checkToASN1.7");
    // uncompressed
    baos = new ByteArrayOutputStream(400);
    try {
      DERSequenceGenerator seq = new DERSequenceGenerator(baos);
      seq.addObject(new ASN1Integer(1));  // version
      seq.addObject(new DEROctetString(k2.getPrivKeyBytes()));
      seq.addObject(new DERTaggedObject(0, curASN1)); 
      seq.addObject(new DERTaggedObject(1, new DERBitString(k2.getPubKey())));
      seq.close();
    } catch(IOException e){
      checkCondition(false, "checkToASN1.8");
    }
    checkCondition(Arrays.equals(bytes2, baos.toByteArray()), "checkToASN1.9");
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
    BigInteger secret = _getRandomSecret();
    key = ECKey.fromPrivate(secret, false);
    checkEquals(key.toString(), _toString(key), "checkToString.4");

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

