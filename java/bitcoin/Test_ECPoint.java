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

  private void checkGetRawXCoord(){ /* TODO */ }
  private void checkGetRawYCoord(){ /* TODO */ }
  private void checkGetXCoord(){ /* TODO */ }
  private void checkGetYCoord(){ /* TODO */ }
  private void checkGetZCoord(){ /* TODO */ }
  private void checkGetZCoords(){ /* TODO */ }
  private void checkHashCode(){ /* TODO */ }
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
