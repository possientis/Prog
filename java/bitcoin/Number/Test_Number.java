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
    checkSignum();
    checkToBytes();
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
    Number x, y, z, t;
    String eName = "NumberFormatException";

    // empty array
    byte [] b0 = {};
    x = Number.fromBytes(1, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.1");
    x = Number.fromBytes(-1, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.2");
    x = Number.fromBytes(0, b0);
    checkEquals(x, Number.ZERO, "checkFromBytes.3");
    checkException(() -> Number.fromBytes(2,b0), eName, "checkFromBytes.4");
    checkException(() -> Number.fromBytes(-2,b0), eName, "checkFromBytes.5");

    // single 0x00 byte
    byte[] b1 = { (byte) 0x00 };
    x = Number.fromBytes(1, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.6");
    x = Number.fromBytes(-1, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.7");
    x = Number.fromBytes(0, b1);
    checkEquals(x, Number.ZERO, "checkFromBytes.8");
    checkException(() -> Number.fromBytes(2,b1), eName, "checkFromBytes.9");
    checkException(() -> Number.fromBytes(-2,b1), eName, "checkFromBytes.10");

    // two 0x00 bytes
    byte[] b2 = { (byte) 0x00, (byte) 0x00 };
    x = Number.fromBytes(1, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.11");
    x = Number.fromBytes(-1, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.12");
    x = Number.fromBytes(0, b2);
    checkEquals(x, Number.ZERO, "checkFromBytes.13");
    checkException(() -> Number.fromBytes(2,b2), eName, "checkFromBytes.14");
    checkException(() -> Number.fromBytes(-2,b2), eName, "checkFromBytes.15");

    // single 0x01 byte
    byte[] b3 = { (byte) 0x01 };
    x = Number.fromBytes(1, b3);
    checkEquals(x, Number.ONE, "checkFromBytes.16");
    checkException(() -> Number.fromBytes(0, b3), eName, "checkFromBytes.17");

    // x + (-x) = 0
    byte[] b4 = getRandomBytes(32); 
    x = Number.fromBytes(1, b4);
    y = Number.fromBytes(-1, b4);
    z = x.add(y);
    checkEquals(z, Number.ZERO, "checkFromBytes.18");

    // multiplying by -1
    z = Number.fromBytes(-1, b3); // -1
    z = z.mul(x);
    checkEquals(y, z, "checkFromBytes.19");

    // padding with 0x00 bytes
    byte[] b5 = getRandomBytes(28);
    x = Number.fromBytes(1, b5);
    y = Number.fromBytes(-1, b5);
    byte[] b6 = new byte[32];
    b6[0] = (byte) 0x00;
    b6[1] = (byte) 0x00;
    b6[2] = (byte) 0x00;
    b6[3] = (byte) 0x00;
    System.arraycopy(b5, 0, b6, 4, 28);
    z = Number.fromBytes(1, b6);
    checkEquals(x, z, "checkFromBytes.20");
    z = Number.fromBytes(-1, b6);
    checkEquals(y, z, "checkFromBytes.21");

    // actual replication
    byte[] b7 = getRandomBytes(32);
    byte[] b8 = new byte[1];
    b8[0] = (byte) 0xFF;
    Number _256 = Number.fromBytes(1, b8).add(Number.ONE);
    x = Number.fromBytes(1, b7);
    y = Number.fromBytes(-1, b7);
    z = Number.ZERO;
    t = Number.ZERO;
    for(int i = 0; i < 32; ++i)
    { 
      b8[0] = b7[i];
      z = z.mul(_256).add(Number.fromBytes(1, b8)); // z = z*256 + b7[i]
      t = t.mul(_256).add(Number.fromBytes(-1,b8)); // t = t*256 - b7[i]
    }
    checkEquals(x, z, "checkFromBytes.22");
    checkEquals(y, t, "checkFromBytes.23");
  }

  private static void checkToBytes(){ /* TODO */ }

  private static void checkSignum()
  {
    byte[] b = getRandomBytes(32);
    Number x = Number.fromBytes(1, b);
    Number y = Number.fromBytes(-1, b);

    checkEquals(x.signum(), 1, "checkSignum.1");
    checkEquals(y.signum(), -1, "checkSignum.2");
    checkEquals(Number.ZERO.signum(), 0, "checkSignum.3");
  }

  private static void checkRandom(){ /* TODO */}
  private static void checkAdd(){ /* TODO */}
  private static void checkMul(){ /* TODO */ }
  private static void checkToString(){ /* TODO */ }
  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkNumberEquals(){ /* TODO */ }


}
