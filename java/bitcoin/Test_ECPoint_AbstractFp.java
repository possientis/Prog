import org.spongycastle.math.ec.ECPoint;

public class Test_ECPoint_AbstractFp extends Test_ECPoint {

  @Override
  public void run()
  {
    logMessage("ECPoint.AbsractFp unit test running ...");
    checkSubtract();
  }

  private void checkSubtract()
  {
    ECPoint x = EC_Test_Utils.getRandomPoint();
    ECPoint y = EC_Test_Utils.getRandomPoint();

    ECPoint check = x.subtract(y);

    checkEquals(check, x.add(y.negate()), "checkSubtract.1");

  }

}
