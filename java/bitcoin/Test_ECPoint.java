import java.math.BigInteger;
import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;


public class Test_ECPoint extends Test_Abstract {

  public void run(){

    logMessage("ECPoint unit test running ...");
    checkECPointAbstractF2m();
    checkECPointAbstractFp();
    checkECPointF2m();
    checkECPointFp();
    checkAdd();
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
  }

  private void checkECPointAbstractFp(){ /* TODO */ }
  private void checkECPointF2m(){ /* TODO */ }
  private void checkECPointFp(){ /* TODO */ }
  private void checkAdd(){ /* TODO */ }
  private void checkECPointEqualsECPoint(){ /* TODO */ }
  private void checkECPointEquals(){ /* TODO */ }
  private void checkGetAffineXCoord(){ /* TODO */ }
  private void checkGetAffineYCoord(){ /* TODO */ }
  private void checkGetCurve(){ /* TODO */ }
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
