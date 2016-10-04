import java.math.BigInteger;

import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;

public class EC_Test_Utils {

  private static void checkCondition(boolean cond, String msg)
  {
    if(!cond) throw new ArithmeticException(msg);
  }

  private static String _getFieldPrimeAsHex(){
    return "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
  }

  private static BigInteger _getFieldPrime(){
    return new BigInteger(_getFieldPrimeAsHex(), 16);
  }

  public static final BigInteger fieldPrime = _getFieldPrime();

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

    boolean isEven1 = (n1.mod(two) == BigInteger.ZERO);
    boolean isEven2 = (n2.mod(two) == BigInteger.ZERO);


    return isEven ? (isEven1 ? n1 : n2) : (isEven1 ? n2 : n1);
  }

  public static BigInteger YFromX(BigInteger x, boolean isEven){

    // returns Y such that Y^2 = X^3 + 7 modulo p of given parity

    BigInteger p = fieldPrime;
    BigInteger seven = BigInteger.valueOf(7);
    BigInteger square = x.multiply(x).mod(p);
    BigInteger cube = square.multiply(x).mod(p);
    BigInteger sum = cube.add(seven);

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


}
