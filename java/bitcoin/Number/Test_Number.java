public class Test_Number extends Test_Abstract
{
  public static void main(String[] args)
  {
    Test_Abstract test = new Test_Number();
    test.run();
  }


  public void run()
  {
    logMessage("Number unit test running ...");
    checkZERO();
    checkONE();
    checkFromBytes();
    checkRandom();
    checkAdd();
    checkMul();
    checkToString();
    checkCompareTo();
    checkHashCode();
    checkNumberEquals();
  }


  private static void checkZERO()
  {
    Number zero = Number.ZERO;
    Number x = Number.random(256);
    Number y = zero.add(x);
    Number z = x.add(zero);
    checkEquals(x, y, "checkZERO.1");
    checkEquals(x, z, "checkZERO.2");
  }

  private static void checkONE()
  {
    Number one = Number.ONE;
    Number x = Number.random(256);
    Number y = one.mul(x);
    Number z = x.mul(one);
    checkEquals(x, y, "checkONE.1");
    checkEquals(x, z, "checkONE.2");
  }

  private static void checkFromBytes()
  {
    byte[] b0 = {};
    Number zero = Number.fromBytes(1, b0);
    checkEquals(zero, Number.ZERO, "checkFromBytes.0");

    byte[] b1 = { (byte) 0x00 };
    Number x = Number.fromBytes(1, b1); // +0
    checkEquals(x, Number.ZERO, "checkFromBytes.1");
    Number y = Number.fromBytes(-1, b1); 
    checkEquals(y, Number.ZERO, "checkFromBytes.2");
//    Number z = Number.fromBytes(2, b1);


  }

  private static void checkRandom(){ /* TODO */}
  private static void checkAdd(){ /* TODO */}
  private static void checkMul(){ /* TODO */ }
  private static void checkToString(){ /* TODO */ }
  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkNumberEquals(){ /* TODO */ }


}
