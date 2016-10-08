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

  private void checkGetDetachedPoint(){ /* TODO */ }
  private void checkGetEncoded(){ /* TODO */ }
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
