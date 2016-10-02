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
    Number x, y, z;
    String eName = "NumberFormatException";

    byte [] b0 = {};
    x = Number.fromBytes(1, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.1");
    x = Number.fromBytes(-1, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.2");
    x = Number.fromBytes(0, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.3");
    checkException(() -> Number.fromBytes(2,b0), eName, "checkFromBytes.4");
    checkException(() -> Number.fromBytes(-2,b0), eName, "checkFromBytes.5");

    byte[] b1 = { (byte) 0x00 };
    x = Number.fromBytes(1, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.6");
    x = Number.fromBytes(-1, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.7");
    x = Number.fromBytes(0, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.8");
    checkException(() -> Number.fromBytes(2,b1), eName, "checkFromBytes.9");
    checkException(() -> Number.fromBytes(-2,b1), eName, "checkFromBytes.10");

    byte[] b2 = { (byte) 0x00, (byte) 0x00 };
    x = Number.fromBytes(1, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.11");
    x = Number.fromBytes(-1, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.12");
    x = Number.fromBytes(0, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.13");
    checkException(() -> Number.fromBytes(2,b2), eName, "checkFromBytes.14");
    checkException(() -> Number.fromBytes(-2,b2), eName, "checkFromBytes.15");

    byte[] b3 = { (byte) 0x01 };
    x = Number.fromBytes(1, b3);
    checkEquals(x, Number.ONE, "checkFromBytes.16");
    checkException(() -> Number.fromBytes(0, b3), eName, "checkFromBytes.17");

    byte[] b4 = getRandomBytes(32); 
    x = Number.fromBytes(1, b4);
    y = Number.fromBytes(-1, b4);
    z = x.add(y);
    checkEquals(z, Number.ZERO, "checkFromBytes.18");
    z = Number.fromBytes(-1, b3); // -1
    z = z.mul(x);
    checkEquals(y, z, "checkFromBytes.19");

    // check left padding with 0x00 TODO

    // check algebra TODO



  }

  private static void checkRandom(){ /* TODO */}
  private static void checkAdd(){ /* TODO */}
  private static void checkMul(){ /* TODO */ }
  private static void checkToString(){ /* TODO */ }
  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkNumberEquals(){ /* TODO */ }


}
