import java.math.BigInteger;
import java.security.SecureRandom;

import org.bitcoin.Secp256k1Context;
import org.bitcoin.NativeSecp256k1;

import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.ECKey;
import org.bitcoin.NativeSecp256k1Util;

import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;
import org.spongycastle.math.ec.custom.sec.SecP256K1Curve;
import org.spongycastle.crypto.digests.SHA256Digest;
import org.spongycastle.crypto.signers.HMacDSAKCalculator;
import org.spongycastle.crypto.signers.ECDSASigner;
import org.spongycastle.crypto.params.ECPrivateKeyParameters;

public class EC_Test_Utils {

  private static final SecureRandom _random = new SecureRandom();

  private static void checkCondition(boolean cond, String msg)
  {
    if(!cond) throw new ArithmeticException(msg);
  }

  private static byte[] getRandomBytes(int n){

    byte[] bytes = new byte[n];

    _random.nextBytes(bytes);

    return bytes;

  }

  public static String getFieldPrimeAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
  }

  public static String getCurveOrderAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"; 
  }

  public static String getCurveGeneratorXAsHex(){
    return "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"; 
  }

  public static String getCurveGeneratorYAsHex(){
    return "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";
  }


  private static BigInteger _getFieldPrime(){
    return new BigInteger(getFieldPrimeAsHex(), 16);
  }

  private static BigInteger _getCurveOrder(){
    return new BigInteger(getCurveOrderAsHex(), 16);
  }

  private static BigInteger _getCurveGeneratorX(){
    return new BigInteger(getCurveGeneratorXAsHex(), 16);
  }

  private static BigInteger _getCurveGeneratorY(){
    return new BigInteger(getCurveGeneratorYAsHex(), 16);
  }


  public static final ECCurve curve = new SecP256K1Curve();
  public static final BigInteger fieldPrime = _getFieldPrime();
  public static final BigInteger curveOrder = _getCurveOrder();
  public static final BigInteger generatorX = _getCurveGeneratorX();
  public static final BigInteger generatorY = _getCurveGeneratorY();
  public static final ECPoint G = curve.createPoint(generatorX, generatorY);
  public static final BigInteger SEVEN = BigInteger.valueOf(7);

  public static ECPoint getRandomPoint()
  {
    BigInteger p = fieldPrime;

    BigInteger x = null;
    BigInteger y = null;

    boolean done = false;

    while(!done)
    {
      byte[] bytes = getRandomBytes(32);

      x = (new BigInteger(1, bytes)).mod(p);

      y = YFromX(x, true);

      if(y != null)
      {
        done = true;
      }
    }
    
    // we have a random point (x,y) but always of even parity. Let's flip a coin

    byte[] parity = getRandomBytes(1);

    // should be evenly distributed

    boolean test = BigInteger.valueOf(parity[0] & 0xFF).testBit(0);

    if(test)
    {
      y = y.negate().mod(p);
    }

    return curve.createPoint(x,y);
  }

  public static BigInteger square(BigInteger n)
  {
    n = n.mod(fieldPrime);

    // there exists a better algorithm for square modulo
    return n.multiply(n).mod(fieldPrime); 
  }


  public static BigInteger sqrt(BigInteger n, boolean isEven){

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

    // retrieving parity of each square root

    boolean isEven1 = !n1.testBit(0);
    boolean isEven2 = !n2.testBit(0);

    BigInteger out = isEven ? (isEven1 ? n1 : n2) : (isEven1 ? n2 : n1);

    // only return 'out' if it is indeed a square root

    return square(out).equals(arg) ? out : null;
  }

  public static BigInteger YFromX(BigInteger x, boolean isEven){

    // returns Y such that Y^2 = X^3 + 7 modulo p of given parity

    BigInteger p = fieldPrime;
    BigInteger square = x.multiply(x).mod(p);
    BigInteger cube = square.multiply(x).mod(p);
    BigInteger sum = cube.add(SEVEN);

    return sqrt(sum, isEven);
  }
  
  public static ECPoint twice(ECPoint point){

    // returns the sum point + point with respect to secp256k1 addition
 
    ECCurve curve = point.getCurve();

    // should not use this function outside of secp256k1 scope
   
    String name = "org.spongycastle.math.ec.custom.sec.SecP256K1Curve"; 

    checkCondition(curve.getClass().getName() == name, "twice.1");

    // point should be normalized

    checkCondition(point.isNormalized(), "twice.2");
     
    // case 1: point is infinity

    if (point.isInfinity()) return curve.getInfinity(); 
    
    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();
    BigInteger p = fieldPrime;

    // expeciting 0 <= x < p and 0 <= y < p

    checkCondition(BigInteger.ZERO.compareTo(x) <= 0, "twice.3");
    checkCondition(x.compareTo(p) < 0, "twice.4");
    checkCondition(BigInteger.ZERO.compareTo(y) <= 0, "twice.5");
    checkCondition(y.compareTo(p) < 0, "twice.6");

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

    return curve.createPoint(X, Y.negate().mod(p));
  }

  public static ECPoint add(ECPoint p1, ECPoint p2){

    // returns the sum p1 + p2 with respect to secp256k1 addition
 
    ECCurve curve = p1.getCurve();

    // both point should be with respect to the same elliptiic curve

    checkCondition(curve.equals(p2.getCurve()), "add.1");

    // should not use this function outside of secp256k1 scope
    
    String name = "org.spongycastle.math.ec.custom.sec.SecP256K1Curve"; 

    checkCondition(curve.getClass().getName() == name, "add.2");

    // point should be normalized
    
    checkCondition(p1.isNormalized(), "add.3");
    checkCondition(p2.isNormalized(), "add.4");

    // case 1: p1 and p2 are equal
 
    if(p1.equals(p2)) return twice(p1);

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

    return curve.createPoint(X, Y.negate().mod(p)); 
  }


  public static ECPoint multiply(BigInteger secret, ECPoint point)
  {
    BigInteger q = curveOrder;
    secret = secret.mod(q);

    ECPoint result = curve.getInfinity(); // identity of the EC group
    ECPoint P = point; // successively equal to point, 2point, 4point, ...

    for(int i = 0; i < 256; ++i)
    {
      if(secret.testBit(0))
      {
        result = add(result, P);
      }

      P = twice(P);

      secret = secret.shiftRight(1);   
    }

    return result;
  }

  public static ECPoint negate(ECPoint point)
  {
 
    if(point.isInfinity()) return curve.getInfinity();

    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();
    BigInteger z = y.negate().mod(fieldPrime);

    return curve.createPoint(x,z);

  }

  public static ECKey.ECDSASignature signNative(
      Sha256Hash input, 
      byte[] priv)
  {

    // being ultra careful before calling native C
    checkCondition(Secp256k1Context.isEnabled(), "_signNative.1");
//    checkNotNull(input, "_signNative.2");
//    checkNotNull(priv, "_signNative.3");
//    checkEquals(priv.length, 32, "_signNative.4");

    try {
      byte[] signature = NativeSecp256k1.sign(input.getBytes(), priv);
      return ECKey.ECDSASignature.decodeFromDER(signature);
    } catch (NativeSecp256k1Util.AssertFailException e){
      checkCondition(false, "_signNative.5");
      return null;
    }
  }


  public static ECKey.ECDSASignature signSpongy(
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


  public static BigInteger getDeterministicKey(
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

  public static BigInteger getProjection(ECPoint point)
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

    BigInteger p = EC_Test_Utils.fieldPrime;

    BigInteger q = ECKey.CURVE.getN();  // seckp256k1 curve order

    BigInteger x = point.getAffineXCoord().toBigInteger();

    // asserting that 0 <= x < p
 
    checkCondition(BigInteger.ZERO.compareTo(x) <= 0, "_getProjection.1");

    checkCondition(x.compareTo(p) == -1, "_getProjection.2");
    
    return x.mod(q);
  }

  public static BigInteger getProjection(Sha256Hash hash)
  {
    // just like in the case of an ECPoint, a message hash needs to 
    // be projected onto the prime field Fq (where q is the curve order)
    // in order to produce a signature. The projection mapping
    // proj : Hash -> Fq is simply a reduction modulo q
    
    BigInteger q = ECKey.CURVE.getN();

    return hash.toBigInteger().mod(q);
  }

  public static ECKey.ECDSASignature signCheck(
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
      BigInteger k = getDeterministicKey(x, message, index++);

      if(k.equals(BigInteger.ZERO)) continue; // start all over

      // get associated ECPoint
      ECPoint point = ECKey.publicPointFromPrivate(k).normalize();

      // signature = (r,s)
      r = getProjection(point);

      if(r.equals(BigInteger.ZERO)) continue; // start all over

      // message hash needs to be projected onto prime field Fq 
      BigInteger e = getProjection(message);

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

}
