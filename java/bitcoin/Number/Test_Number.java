import java.util.Arrays;
import java.math.BigInteger;

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
    checkFromBigInteger();
    checkToBigInteger();
    checkBitLength();
  }

  private static Number _signedRandom(int numBits)
  {
    Number x = Number.random(numBits);
    Number flip = Number.random(1);
    return flip.equals(Number.ONE) ? x.negate() : x;
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


    // using toBytes and signum
    byte[] b9 = getRandomBytes(32);
    x = Number.fromBytes(1, b9);
    y = Number.fromBytes(-1, b9);

    checkEquals(x.signum(), 1, "checkFromBytes.24");
    checkEquals(y.signum(), -1, "checkFromBytes.25");

    byte[] b10 = x.toBytes(32);
    byte[] b11 = y.toBytes(32);

    checkCondition(Arrays.equals(b9, b10), "checkFromBytes.26");
    checkCondition(Arrays.equals(b9, b11), "checkFromBytes.27");
  }

  private static void checkToBytes()
  {
    String eName = "ArithmeticException";
    byte[] bytes;

    // ZERO
    bytes = Number.ZERO.toBytes(0);
    checkEquals(bytes.length, 0, "checkToBytes.1");

    bytes = Number.ZERO.toBytes(32);
    checkEquals(bytes.length, 32, "checkToBytes.2");
    for(int i = 0; i < 32; ++i)
    {
      checkEquals(bytes[i], (byte) 0x00, "checkToBytes.3");
    }

    // ONE
    checkException(() -> Number.ONE.toBytes(0), eName, "checkToBytes.4");
    bytes = Number.ONE.toBytes(1);
    checkEquals(bytes.length, 1, "checkToBytes.5");
    checkEquals(bytes[0], (byte) 0x01, "checkToBytes.6");
    bytes = Number.ONE.negate().toBytes(1);
    checkEquals(bytes.length, 1, "checkToBytes.7");
    checkEquals(bytes[0], (byte) 0x01, "checkToBytes.8");
    bytes = Number.ONE.toBytes(32);
    checkEquals(bytes.length, 32, "checkToBytes.9");
    checkEquals(bytes[31], (byte) 0x01, "checkToBytes.10"); // big-endian
    for(int i = 0; i < 31; ++i)
    {
      checkEquals(bytes[i], (byte) 0x00, "checkToBytes.11");
    }

    // random
    Number x = Number.random(256);
    Number y = x.negate();
    bytes = x.toBytes(32);
    checkEquals(x, Number.fromBytes(1, bytes), "checkToBytes.12");
    checkEquals(y, Number.fromBytes(-1, bytes), "checkToBytes.13");
    bytes = y.toBytes(32);
    checkEquals(x, Number.fromBytes(1, bytes), "checkToBytes.14");
    checkEquals(y, Number.fromBytes(-1, bytes), "checkToBytes.15");
  }

  private static void checkSignum()
  {


    checkEquals(Number.ZERO.signum(), 0, "checkSignum.3");

    byte[] b = getRandomBytes(32);
    Number x = Number.fromBytes(1, b);
    Number y = Number.fromBytes(-1, b);

    checkEquals(x.signum(), 1, "checkSignum.1");
    checkEquals(y.signum(), -1, "checkSignum.2");
  }

  private static void checkRandom(){
    // checking a random generator should be far more involved
    // than anything done here.

    Number x;
    x = Number.random(0);
    checkEquals(x, Number.ZERO, "checkRandom.1");

    x = Number.random(1);   // single bit
    checkCondition(x.equals(Number.ZERO)||x.equals(Number.ONE), "checkRandom.2");

    x = Number.random(256);
    checkEquals(x.signum(), 1, "checkRandom.3");

    int count = 0;
    for(int i = 0; i < 10000; ++i)
    {
      x = Number.random(256);
      byte[] bytes = x.toBytes(32);
      
      Number y = Number.random(5);              // selecting byte 0 to 31
      int index = y.toBytes(1)[0] & 0xFF;       // 0 to 31
      int test = bytes[index] & 0xFF;
      Number z = Number.random(3);              // selecting bit 0...7
      int bit = z.toBytes(1)[0] & 0xFF;         // 0 to 7
      if(BigInteger.valueOf(test).testBit(bit)) // inefficient but highly readable
      {
        ++count;
      }
    }

    // should be able to compute upper-bound on probability of failure
    checkCondition(count > 4800, "checkRandom.4");
    checkCondition(count < 5200, "checkRandom.5");
  }

  private static void checkAdd()
  {

    Number x = _signedRandom(256);
    Number y = _signedRandom(256);
    Number z = _signedRandom(256);

    // x + 0 = x
    checkEquals(x.add(Number.ZERO), x, "checkAdd.1");

    // 0 + x = x
    checkEquals(Number.ZERO.add(x), x, "checkAdd.2");

    // x + (-x) = 0
    checkEquals(x.add(x.negate()), Number.ZERO, "checkAdd.3");

    // (-x) + x = 0
    checkEquals(x.negate().add(x), Number.ZERO, "checkAdd.4");

    // x + y = y + x
    checkEquals(x.add(y), y.add(x), "checkAdd.5");

    // (x + y) + z = x + (y + z)
    checkEquals(x.add(y).add(z), x.add(y.add(z)), "checkAdd.6");

    // actual check of x + y
    BigInteger n = new BigInteger(x.signum(), x.toBytes(32));
    BigInteger m = new BigInteger(y.signum(), y.toBytes(32));
    BigInteger sum = n.add(m);
    Number check;

    if(sum.compareTo(BigInteger.ZERO) >= 0)
    {
      check = Number.fromBytes(1, sum.toByteArray());
    }
    else
    {
      check = Number.fromBytes(-1, sum.negate().toByteArray());
    }

    checkEquals(check, x.add(y), "checkAdd.7");

  }

  private static void checkMul()
  {
    Number x = _signedRandom(256);
    Number y = _signedRandom(256);
    Number z = _signedRandom(256);

    // x * 0  = 0
    checkEquals(x.mul(Number.ZERO), Number.ZERO, "checkMul.1");

    // 0 * x = 0
    checkEquals(Number.ZERO.mul(x), Number.ZERO, "checkMul.2");

    // x * 1  = x
    checkEquals(x.mul(Number.ONE), x, "checkMul.3");

    // 1 * x = x
    checkEquals(Number.ONE.mul(x), x, "checkMul.4");

    // (-x) * (-y) = x * y
    checkEquals(x.negate().mul(y.negate()), x.mul(y), "checkMul.5");

    // x * y = y * x
    checkEquals(x.mul(y), y.mul(x), "checkMul.6");

    // (x * y) * z = x * (y * z)
    checkEquals(x.mul(y).mul(z), x.mul(y.mul(z)), "checkMul.7");

    // actual check of x * y
    BigInteger n = new BigInteger(x.signum(), x.toBytes(32));
    BigInteger m = new BigInteger(y.signum(), y.toBytes(32));
    BigInteger prod = n.multiply(m);
    Number check = Number.fromBigInteger(prod);
    checkEquals(check, x.mul(y), "checkMul.8");
  }

  private static void checkToString()
  {
    String check1;
    String check2;
    Number x;

    // zero
    check1 = Number.ZERO.toString();
    checkEquals(check1, "0", "checkToString.1");

    // one
    check1 = Number.ONE.toString();
    checkEquals(check1, "1", "checkToString.1");

    // random positive
    x = Number.random(256);
    

  }


  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkNumberEquals(){ /* TODO */ }
  private static void checkFromBigInteger(){ /* TODO */ }
  private static void checkToBigInteger(){ /* TODO */ }
  private static void checkBitLength(){ /* TODO */ }

}
