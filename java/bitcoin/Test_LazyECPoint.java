import java.util.Arrays;
import java.math.BigInteger;

import org.spongycastle.math.ec.ECCurve;
import org.spongycastle.math.ec.ECFieldElement;
import org.spongycastle.math.ec.ECPoint;

import org.bitcoinj.crypto.LazyECPoint;


public class Test_LazyECPoint extends Test_Abstract {

  public void run()
  {
    logMessage("LazyECPoint unit test running ...");
    checkLazyECPointFromBytes();
    checkLazyECPointFromECPoint();
    checkAdd();
    checkLazyECPointEqualsECPoint();
    checkLazyECPointEqualsObject();
    checkGet();
    checkGetAffineXCoord();
    checkGetAffineYCoord();
    checkGetCurve();
    checkGetDetachedPoint();
    checkGetEncoded();
    checkGetEncodedFromBoolean();
    checkGetX();
    checkGetXCoord();
    checkGetY();
    checkGetYCoord();
    checkGetZCoord();
    checkGetZCoords();
    checkHashCode();
    checkIsCompressed();
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
    checkTwice();
    checkTwicePlus();
  }

  private void checkLazyECPointFromBytes()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    ECCurve curve = EC_Test_Utils.curve;


    byte[] bytes = point.getEncoded(false); // uncompressed
    LazyECPoint lazy = new LazyECPoint(curve, bytes);
    checkEquals(point, lazy.get(), "checkLazyECPointFromBytes.1");

    bytes = point.getEncoded(true);         // compressed
    lazy = new LazyECPoint(curve, bytes);
    checkEquals(point, lazy.get(), "checkLazyECPointFromBytes.2");
  }

  private void checkLazyECPointFromECPoint()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    checkEquals(point, lazy.get(), "checkLazyECPointFromECPoint.1");
  }

  private void checkAdd()
  {
    ECPoint check1;
    ECPoint check2;

    LazyECPoint zero = new LazyECPoint(EC_Test_Utils.curve.getInfinity());

    LazyECPoint x = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    LazyECPoint y = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    LazyECPoint z = new LazyECPoint(EC_Test_Utils.getRandomPoint());

    // 0 + x = x
    check1 = zero.add(x.get());
    checkEquals(check1, x.get(), "checkAdd.1");

    // x + 0 = x
    check1 = x.add(zero.get());
    checkEquals(check1, x.get(), "checkAdd.2");


    // x + (-x) = 0
    check1 = x.add(x.negate());
    checkEquals(check1, zero.get(), "checkAdd.3");

    // (-x) + x = 0
    check1 = x.negate().add(x.get());
    checkEquals(check1, zero.get(), "checkAdd.4");

    // x + y = y + x
    checkEquals(x.add(y.get()), y.add(x.get()), "checkAdd.5");

    // (x + y) + z = x + (y + z)
    check1 = x.add(y.get()).add(z.get());
    check2 = x.add(y.add(z.get()));
    checkEquals(check1, check2, "checkAdd.6");

    // abelian group properties seemingly satisfied, but
    // many wrong implementation will achieve as much

    check1 = x.add(y.get());
    check2 = EC_Test_Utils.add(x.get(),y.get());
    checkEquals(check1, check2, "checkAdd.7");
 
  }

  private void checkLazyECPointEqualsECPoint()
  {
    // not doing much here
    LazyECPoint x = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    LazyECPoint y = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    checkCondition(!x.equals(y.get()), "checkLazyECPointEqualsECPoint.1");
    checkCondition(!y.equals(x.get()), "checkLazyECPointEqualsECPoint.2");
    checkCondition(x.equals(x.get()), "checkLazyECPointEqualsECPoint.3");
    checkCondition(y.equals(y.get()), "checkLazyECPointEqualsECPoint.4");
 }

  private void checkLazyECPointEqualsObject()
  {
    // not doing much here
    Object x = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    Object y = new LazyECPoint(EC_Test_Utils.getRandomPoint());
    checkCondition(!x.equals(y), "checkLazyECPointEqualsObject.1");
    checkCondition(!y.equals(x), "checkLazyECPointEqualsObject.2");
    checkCondition(x.equals(x), "checkLazyECPointEqualsObject.3");
  }

  private void checkGet()
  {
    ECCurve curve = EC_Test_Utils.curve;
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    checkEquals(point, lazy.get(), "checkGet.1");
    lazy = new LazyECPoint(curve, point.getEncoded(false)); // uncompressed
    checkEquals(point, lazy.get(), "checkGet.2");
    lazy = new LazyECPoint(curve, point.getEncoded(true)); // compressed
    checkEquals(point, lazy.get(), "checkGet.3");
  }

  private void checkGetAffineXCoord()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    ECFieldElement x1 = lazy.getAffineXCoord(); 
    ECFieldElement x2 = point.getAffineXCoord(); 
    checkEquals(x1, x2, "checkGetAffineXCoord.1");

    point = point.add(point); // no longer normalized
    LazyECPoint lazy2 = new LazyECPoint(point);
    checkException(
        () -> lazy2.getAffineXCoord(), 
        "IllegalStateException",
        "checkGetAffineXCoord.2"
    );
  }

  private void checkGetAffineYCoord()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    ECFieldElement y1 = lazy.getAffineYCoord(); 
    ECFieldElement y2 = point.getAffineYCoord(); 
    checkEquals(y1, y2, "checkGetAffineYCoord.1");
    point = point.add(point); // no longer normalized
    LazyECPoint lazy2 = new LazyECPoint(point);
    checkException(
        () -> lazy2.getAffineYCoord(), 
        "IllegalStateException",
        "checkGetAffineYCoord.2"
    );
 
  }

  private void checkGetCurve()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    checkEquals(lazy.getCurve(), point.getCurve(), "checkGetCurve.1"); 
  }

  private void checkGetDetachedPoint()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    point = point.add(point); // not normalized
    LazyECPoint lazy = new LazyECPoint(point);
    ECPoint p1 = point.getDetachedPoint();  // normalized clone
    ECPoint p2 = lazy.getDetachedPoint();   // normalized clone
    checkEquals(p1, p2, "checkGetDetachedPoint.1"); 
    checkCondition(p1.isNormalized(), "checkGetDetachedPoint.2");
    checkCondition(p2.isNormalized(), "checkGetDetachedPoint.3");
  }

  private void checkGetEncoded()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);

    // TODO work out exact semantics of getEncoded()
    byte[] bytes1 = point.getEncoded(false); // compressed
    byte[] bytes2 = lazy.getEncoded();

    BigInteger n1 = new BigInteger(1, bytes1);
    BigInteger n2 = new BigInteger(1, bytes2);

    logMessage(n1.toString(16));
    logMessage(n2.toString(16));

    checkCondition(Arrays.equals(bytes1, bytes2), "checkGetEncoded.1");
  }

  private void checkGetEncodedFromBoolean()
  {
    ECPoint point = EC_Test_Utils.getRandomPoint();
    LazyECPoint lazy = new LazyECPoint(point);
    byte[] bytes1;
    byte[] bytes2;

    bytes1 = point.getEncoded(false); // uncompressed
    bytes2 = lazy.getEncoded(false);
    checkCondition(Arrays.equals(bytes1, bytes2), "checkGetEncodedFromBoolean.1");

 
    bytes1 = point.getEncoded(true); // compressed
    bytes2 = lazy.getEncoded(true);

    checkCondition(Arrays.equals(bytes1, bytes2), "checkGetEncodedFromBoolean.2");
  }

  private void checkGetX(){ /* TODO */ }
  private void checkGetXCoord(){ /* TODO */ }
  private void checkGetY(){ /* TODO */ }
  private void checkGetYCoord(){ /* TODO */ }
  private void checkGetZCoord(){ /* TODO */ }
  private void checkGetZCoords(){ /* TODO */ }
  private void checkHashCode(){ /* TODO */ }
  private void checkIsCompressed(){ /* TODO */ }
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
  private void checkTwice(){ /* TODO */ }
  private void checkTwicePlus(){ /* TODO */ }


}
