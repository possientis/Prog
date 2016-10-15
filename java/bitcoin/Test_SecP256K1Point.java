import org.spongycastle.math.ec.ECPoint;
import org.spongycastle.math.ec.ECCurve;

public class Test_SecP256K1Point extends Test_ECPoint_AbstractFp {

  @Override public void run()
  {
    logMessage("SecP256K1Point unit test running ...");

    checkAdd();
    checkNegate();
    checkThreeTimes();
    checkTwice();
    checkTwicePlus();
  }
 

  private void checkAdd()
  {
    ECPoint check1;
    ECPoint check2;

    ECPoint zero = EC_Test_Utils.curve.getInfinity();

    ECPoint x = EC_Test_Utils.getRandomPoint();
    ECPoint y = EC_Test_Utils.getRandomPoint();
    ECPoint z = EC_Test_Utils.getRandomPoint();

    // 0 + x = x
    check1 = zero.add(x);
    checkEquals(check1, x, "checkAdd.1");

    // x + 0 = x
    check1 = x.add(zero);
    checkEquals(check1, x, "checkAdd.2");


    // x + (-x) = 0
    check1 = x.add(x.negate());
    checkEquals(check1, zero, "checkAdd.3");

    // (-x) + x = 0
    check1 = x.negate().add(x);
    checkEquals(check1, zero, "checkAdd.4");

    // x + y = y + x
    checkEquals(x.add(y), y.add(x), "checkAdd.5");

    // (x + y) + z = x + (y + z)
    check1 = x.add(y).add(z);
    check2 = x.add(y.add(z));
    checkEquals(check1, check2, "checkAdd.6");

    // abelian group properties seemingly satisfied, but
    // many wrong implementation will achieve as much

    check1 = x.add(y);
    check2 = EC_Test_Utils.add(x,y);
    checkEquals(check1, check2, "checkAdd.7");
    
  }

  private void checkNegate()
  {
    ECPoint zero = EC_Test_Utils.curve.getInfinity();

    ECPoint x = EC_Test_Utils.getRandomPoint();

    // -0 = 0
    checkEquals(zero.negate(), zero, "checkNegate.1");

    // -(-x) = x
    checkEquals(x.negate().negate(), x, "checkNegate.2");

    // x + (-x) = 0
    checkEquals(x.add(x.negate()), zero, "checkNegate.3");


    // actual check
    checkEquals(x.negate(), EC_Test_Utils.negate(x), "checkNegate.4");
 
  }

  private void checkThreeTimes()
  {
    ECPoint x = EC_Test_Utils.getRandomPoint();

    ECPoint check = x.threeTimes();

    checkEquals(check, x.add(x.add(x)), "checkThreeTimes.1");
  }

  private void checkTwice()
  {
    ECPoint x = EC_Test_Utils.getRandomPoint();

    ECPoint check = x.twice();

    checkEquals(check, x.add(x), "checkTwice.1");

    checkEquals(check, EC_Test_Utils.twice(x), "checkTwice.2");

   }

  private void checkTwicePlus()
  {
    ECPoint x = EC_Test_Utils.getRandomPoint();
    ECPoint y = EC_Test_Utils.getRandomPoint();

    ECPoint check = x.twicePlus(y);

    checkEquals(check, x.twice().add(y), "checkTwicePlus.1");
  }

}
