import java.util.Arrays;
import java.math.BigInteger;
import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;
import org.spongycastle.math.ec.ECFieldElement;


public class Test_ECPoint extends Test_Abstract {

  public void run(){

    logMessage("ECPoint unit test running ...");
    checkECPointAbstractF2m();
    checkECPointAbstractFp();
    checkECPointF2m();
    checkECPointFp();
    checkECPointEqualsECPoint();
    checkECPointEquals();
    checkGetAffineXCoord();
    checkGetAffineYCoord();
    checkGetCurve();
    checkGetDetachedPoint();
    checkGetEncoded();
    checkGetRawXCoord();
    checkGetRawYCoord();
    checkGetXCoord();
    checkGetYCoord();
    checkGetZCoord();
    checkGetZCoords();
    checkHashCode();
    checkIsInfinity();
    checkIsNormalized();
    checkIsValid();
    checkMultiply();
    checkNegate();
    checkNormalize();
    checkScaleX();
    checkScaleY();
    checkSubtract();
    checkThreeTimes();
    checkTimesPow2();
    checkToString();
    checkTwice();
    checkTwicePlus();
  }


  protected static ECPoint _getRandomPoint()
  {
    ECCurve curve = EC_Test_Utils.curve;

    BigInteger p = EC_Test_Utils.fieldPrime;

    BigInteger x = null;
    BigInteger y = null;

    boolean done = false;

    while(!done)
    {
      byte[] bytes = getRandomBytes(32);

      x = (new BigInteger(1, bytes)).mod(p);

      y = EC_Test_Utils.YFromX(x, true);

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

  private void checkECPointAbstractF2m()
  {
    ECPoint.AbstractF2m x;  // compile time check
  }

  private void checkECPointAbstractFp()
  {
    ECPoint.AbstractFp x;   // compile time check
  }

  private void checkECPointF2m()
  {
    ECPoint.F2m x;          // compile time check
  }
  private void checkECPointFp()
  {
    ECPoint.Fp x;           // compile time check
  }

  private void checkECPointEqualsECPoint()
  {
    // not doing much here
    ECPoint x = _getRandomPoint();
    ECPoint y = _getRandomPoint();
    checkCondition(!x.equals(y), "checkECPointEqualsECPoint.1");
    checkCondition(!y.equals(x), "checkECPointEqualsECPoint.2");
    checkCondition(x.equals(x), "checkECPointEqualsECPoint.3");
    checkCondition(y.equals(y), "checkECPointEqualsECPoint.4");
  }

  private void checkECPointEquals()
  {
    // not doing much here
    Object x = _getRandomPoint();
    Object y = _getRandomPoint();
    checkCondition(!x.equals(y), "checkECPointEquals.1");
    checkCondition(!y.equals(x), "checkECPointEquals.2");
    checkCondition(x.equals(x), "checkECPointEquals.3");
    checkCondition(y.equals(y), "checkECPointEquals.4");
  }

  private void checkGetAffineXCoord()
  {
    ECCurve curve = EC_Test_Utils.curve;
    ECPoint point = _getRandomPoint();
    ECFieldElement x = point.getAffineXCoord();
    ECFieldElement y = point.getAffineYCoord();

    BigInteger xx = x.toBigInteger();
    BigInteger yy = y.toBigInteger();

    ECPoint test = curve.createPoint(xx,yy);

    checkEquals(x, test.getAffineXCoord(), "checkGetAffineXCoord.1");

    // some algebraic operation, result of which is not normalized
    ECPoint test2 = test.add(test);
    checkCondition(!test2.isNormalized(), "checkGetAffineXCoord.2");

    // function should throw on non-normalized input
    checkException(
        () -> test2.getAffineXCoord(), 
        "IllegalStateException",
        "checkGetAffineXCoord.3"
    );
  }

  private void checkGetAffineYCoord()
  {
    ECCurve curve = EC_Test_Utils.curve;
    ECPoint point = _getRandomPoint();
    ECFieldElement x = point.getAffineXCoord();
    ECFieldElement y = point.getAffineYCoord();

    BigInteger xx = x.toBigInteger();
    BigInteger yy = y.toBigInteger();

    ECPoint test = curve.createPoint(xx,yy);

    checkEquals(y, test.getAffineYCoord(), "checkGetAffineYCoord.1");

    // some algebraic operation, result of which is not normalized
    ECPoint test2 = test.add(test);
    checkCondition(!test2.isNormalized(), "checkGetAffineYCoord.2");

    // function should throw on non-normalized input
    checkException(
        () -> test2.getAffineYCoord(), 
        "IllegalStateException",
        "checkGetAffineYCoord.3"
    );
  }

  private void checkGetCurve()
  {
    ECCurve curve = EC_Test_Utils.curve;
    ECPoint G = EC_Test_Utils.G;
    ECPoint P = _getRandomPoint();
    checkEquals(curve, G.getCurve(), "checkGetCurve.1");
    checkEquals(curve, P.getCurve(), "checkGetCurve.2");
  }

  private void checkGetDetachedPoint()
  {
    // returns a normalized clone it seems

    ECPoint point = _getRandomPoint();

    point = point.add(point); // no longer normalized

    checkCondition(!point.isNormalized(), "checkGetDetachedPoint.1");

    ECPoint cloned = point.getDetachedPoint();

    // cloned should be normalized
    checkCondition(cloned.isNormalized(), "checkGetDetachedPoint.2");

    // cloned is essentially the same point
    checkEquals(point, cloned, "checkGetDetachedPoint.3");

    // cloned is a new reference
    checkCondition(point != cloned, "checkGetDetachedPoint.4");
  }

  private void checkGetEncoded()
  {
    // infinity
    ECPoint zero = EC_Test_Utils.curve.getInfinity();
    byte[] z1 = zero.getEncoded(true);
    byte[] z2 = zero.getEncoded(false);
    checkEquals(z1.length, 1, "checkGetEncoded.1");
    checkEquals(z2.length, 1, "checkGetEncoded.2");
    checkEquals(z1[0], (byte) 0x00, "checkGetEncoded.3");
    checkEquals(z2[0], (byte) 0x00, "checkGetEncoded.4");


    // random
    ECPoint point = _getRandomPoint();
    byte[] b1 = point.getEncoded(true);   // compressed
    byte[] b2 = point.getEncoded(false);  // uncompressed

    boolean parity = point.getAffineYCoord().testBitZero();

    // checking sizes
    checkEquals(b1.length, 33, "checkGetEncoded.5");
    checkEquals(b2.length, 65, "checkGetEncoded.6");

    // checking leading bytes
    byte first = parity ? (byte) 0x03 : (byte) 0x02;
    checkEquals(b1[0], first, "checkGetEncoded.7");
    checkEquals(b2[0], (byte) 0x04, "checkGetEncoded.8");

    // checking X
    byte[] bx = point.getAffineXCoord().getEncoded();
    checkEquals(bx.length, 32, "checkGetEncoded.9");
    for(int i = 0; i < 32; ++i)
    {
      checkEquals(bx[i], b1[i+1], "checkGetEncoded.10");
      checkEquals(bx[i], b2[i+1], "checkGetEncoded.11");
    }

    // checking Y
    byte[] by = point.getAffineYCoord().getEncoded();
    checkEquals(by.length, 32, "checkGetEncoded.12");
    for(int i = 0; i < 32; ++i)
    {
      checkEquals(by[i], b2[i+33], "checkGetEncoded.13");
    }

    // encoding is that of normalized point
    point = point.add(point);  // no longer normalized

    checkCondition(!point.isNormalized(), "checkGetEncoded.14");

    b1 = point.getEncoded(true);    // compressed
    b2 = point.getEncoded(false);   // uncompressed

    byte[] test1 = point.normalize().getEncoded(true);
    byte[] test2 = point.normalize().getEncoded(false);

    checkCondition(Arrays.equals(b1, test1), "checkGetEncoded.15");
    checkCondition(Arrays.equals(b2, test2), "checkGetEncoded.16");
  }

  private void checkGetRawXCoord()
  {
    // normalized
    ECPoint point = _getRandomPoint();
    checkCondition(point.isNormalized(), "checkGetRawXCoord.1");
    ECFieldElement x1 = point.getRawXCoord();
    ECFieldElement x2 = point.getAffineXCoord();
    ECFieldElement x3 = point.getXCoord();
    checkEquals(x1, x2, "checkGetRawXCoord.2");
    checkEquals(x1, x3, "checkGetRawXCoord.3");

    // not normalized
    point = point.add(point);
    checkCondition(!point.isNormalized(), "checkGetRawXCoord.4");
    x1 = point.getRawXCoord();
    x2 = point.normalize().getAffineXCoord();
    x3 = point.getXCoord();
    checkCondition(!x1.equals(x2), "checkGetRawXCoord.5");
    checkEquals(x1, x3, "checkGetRawXCoord.6");
  }

  private void checkGetRawYCoord()
  {
    // normalized
    ECPoint point = _getRandomPoint();
    checkCondition(point.isNormalized(), "checkGetRawXCoord.1");
    ECFieldElement x1 = point.getRawXCoord();
    ECFieldElement x2 = point.getAffineXCoord();
    ECFieldElement x3 = point.getXCoord();
    checkEquals(x1, x2, "checkGetRawXCoord.2");
    checkEquals(x1, x3, "checkGetRawXCoord.3");

    // not normalized
    point = point.add(point);
    checkCondition(!point.isNormalized(), "checkGetRawXCoord.4");
    x1 = point.getRawXCoord();
    x2 = point.normalize().getAffineXCoord();
    x3 = point.getXCoord();
    checkCondition(!x1.equals(x2), "checkGetRawXCoord.5");
    checkEquals(x1, x3, "checkGetRawXCoord.6");
  }

  private void checkGetXCoord()
  {
    checkGetRawXCoord();
  }

  private void checkGetYCoord()
  {
    checkGetRawYCoord();
  }

  private void checkGetZCoord()
  {
    ECPoint point = _getRandomPoint(); // normalized

    BigInteger z = point.getZCoord(0).toBigInteger();
    checkEquals(z, BigInteger.ONE, "checkGetZCoord.1");
    checkCondition(point.getZCoord(1) == null, "checkGetZCoord.2"); 

    point = point.add(point);         // no longer normalized
    z = point.getZCoord(0).toBigInteger();
    BigInteger x = point.getXCoord().toBigInteger();
    BigInteger y = point.getYCoord().toBigInteger();
    BigInteger _7 = BigInteger.valueOf(7);
    BigInteger p = EC_Test_Utils.fieldPrime;
    BigInteger y2 = y.multiply(y).mod(p);
    BigInteger x3 = x.multiply(x).multiply(x).mod(p);
    BigInteger z2 = z.multiply(z).mod(p);
    BigInteger z6 = z2.multiply(z2).multiply(z2).mod(p);
    BigInteger check = x3.add(_7.multiply(z6).mod(p)).mod(p);
    checkEquals(check, y2, "checkGetZCoord.3"); // Y^2 = X^3 + 7.Z^6
    point = point.normalize();
    BigInteger u = point.getXCoord().toBigInteger();
    BigInteger v = point.getYCoord().toBigInteger();
    BigInteger zInv = z.modInverse(p);
    BigInteger zInv2 = zInv.multiply(zInv).mod(p);
    BigInteger zInv3 = zInv2.multiply(zInv).mod(p);
    y = y.multiply(zInv3).mod(p);
    x = x.multiply(zInv2).mod(p);
    checkEquals(x, u, "checkGetZCoord.4");  // X' = X/Z^2
    checkEquals(y, v, "checkGetZCoord.5");  // Y' = Y/Z^3
  }

  private void checkGetZCoords()
  {
    ECPoint point = _getRandomPoint();  // normalized

    ECFieldElement[] zs = point.getZCoords();
    checkEquals(zs.length, 1, "checkGetZCoords.1");
    BigInteger z = zs[0].toBigInteger();
    checkEquals(z, BigInteger.ONE, "checkGetZCoords.2");

    point = point.add(point); // no longer normalized
    zs = point.getZCoords();
    checkEquals(zs.length, 1, "checkGetZCoords.3");
    checkEquals(zs[0], point.getZCoord(0), "checkGetZCoords.4");
  }

  private void checkHashCode()
  {
    ECPoint point = _getRandomPoint();      // normalized
    point = point.add(point);               // no longer normalized;
    int check = point.hashCode();
    int hc = ~point.getCurve().hashCode();  // one's complement of curve hash 

    point = point.normalize();

    hc ^= point.getXCoord().hashCode() * 17;
    hc ^= point.getYCoord().hashCode() * 257;

    checkEquals(check, hc, "checkHashCode.1");
  }


  private void checkIsInfinity(){ /* TODO */ }
  private void checkIsNormalized(){ /* TODO */ }
  private void checkIsValid(){ /* TODO */ }
  private void checkMultiply(){ /* TODO */ }
  private void checkNegate(){ /* TODO */ }
  private void checkNormalize(){ /* TODO */ }
  private void checkScaleX(){ /* TODO */ }
  private void checkScaleY(){ /* TODO */ }
  private void checkSubtract(){ /* TODO */ }
  private void checkThreeTimes(){ /* TODO */ }
  private void checkTimesPow2(){ /* TODO */ }
  private void checkToString(){ /* TODO */ }
  private void checkTwice(){ /* TODO */ }
  private void checkTwicePlus(){ /* TODO */ }



}
