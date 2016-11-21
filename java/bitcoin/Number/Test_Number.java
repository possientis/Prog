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

  private static void checkSignum()
  {
    checkEquals(Number.ZERO.signum(), 0, "checkSignum.1");

    byte[] b = getRandomBytes(32);
    Number x = Number.fromBytes(1, b);
    Number y = Number.fromBytes(-1, b);

    checkEquals(x.signum(), 1, "checkSignum.2");
    checkEquals(y.signum(), -1, "checkSignum.3");
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
        ++count;                                // should be 50% chance occurence
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
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    BigInteger sum = n.add(m);
    Number check = Number.fromBigInteger(sum);
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

    // (x + y) * z = (x * z) + (y * z)
    checkEquals(x.add(y).mul(z), x.mul(z).add(y.mul(z)), "checkMul.8"); 

    // actual check of x * y
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    BigInteger prod = n.multiply(m);
    Number check = Number.fromBigInteger(prod);
    checkEquals(check, x.mul(y), "checkMul.9");
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
    checkEquals(check1, "1", "checkToString.2");

    // minus one
    check1 = Number.ONE.negate().toString();
    checkEquals(check1, "-1", "checkToString.3");

    // random positive
    x = Number.random(256);
    check1 = x.toString();
    check2 = x.toBigInteger().toString();
    checkEquals(check1, check2, "checkToString.4");
  }

  private static void checkCompareTo()
  {

    // from random
    Number x = Number.random(256);  
    Number y = x.negate();

    checkEquals(x.compareTo(Number.ZERO), 1, "checkCompareTo.1");
    checkEquals(Number.ZERO.compareTo(x), -1, "checkCompareTo.2");
    checkEquals(y.compareTo(Number.ZERO), -1, "checkCompareTo.3");
    checkEquals(Number.ZERO.compareTo(y), 1, "checkCompareTo.4");

    // from bytes
    byte[] bytes = getRandomBytes(32);
    x = Number.fromBytes(1, bytes);
    y = Number.fromBytes(-1, bytes);

    checkEquals(x.compareTo(Number.ZERO), 1, "checkCompareTo.5");
    checkEquals(Number.ZERO.compareTo(x), -1, "checkCompareTo.6");
    checkEquals(y.compareTo(Number.ZERO), -1, "checkCompareTo.7");
    checkEquals(Number.ZERO.compareTo(y), 1, "checkCompareTo.8");

    // from _signedRandom
    x = _signedRandom(256);
    y = _signedRandom(256);

    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();

    checkEquals(x.compareTo(y), n.compareTo(m), "checkCompareTo.9");
    checkEquals(y.compareTo(x), m.compareTo(n), "checkCompareTo.10");


    y = Number.fromBigInteger(n);
    checkEquals(x.compareTo(y), 0, "checkCompareTo.11");
    checkEquals(y.compareTo(x), 0, "checkCompareTo.12");

    // 0 <= 1
    checkEquals(Number.ZERO.compareTo(Number.ONE), -1, "checkCompareTo.13");
    checkEquals(Number.ONE.compareTo(Number.ZERO), 1, "checkCompareTo.14");
  }

  private static void checkHashCode()
  {
    // 0 and 1
    int hash1 = Number.ZERO.hashCode();
    int hash2 = Number.ONE.hashCode();

    checkCondition(hash1 != hash2, "checkHashCode.1");

    // x and - x
    Number x = _signedRandom(256);
    hash1 = x.hashCode();
    hash2 = x.negate().hashCode();
    checkCondition(hash1 != hash2, "checkHashCode.2");
    
    // same number
    BigInteger n = x.toBigInteger();
    Number y = Number.fromBigInteger(n);
    hash1 = x.hashCode();
    hash2 = y.hashCode();
    checkEquals(hash1, hash2, "checkHashCode.3");
  }

  private static void checkNumberEquals()
  {
    // 0 and 1
    checkCondition(!Number.ZERO.equals(Number.ONE), "checkNumberEquals.1");
    checkCondition(!Number.ONE.equals(Number.ZERO), "checkNumberEquals.2");

    // x and -x
    Number x = _signedRandom(256);
    checkCondition(!x.equals(x.negate()), "checkNumberEquals.3");
    checkCondition(!x.negate().equals(x), "checkNumberEquals.4");

    // same number
    BigInteger n = x.toBigInteger();
    Number y = Number.fromBigInteger(n);
    checkCondition(x.equals(y), "checkNumberEquals.5");
    checkCondition(y.equals(x), "checkNumberEquals.6");
    checkCondition(x.equals(x), "checkNumberEquals.7");
    checkEquals(x, y, "checkNumberEquals.8");
    checkEquals(y, x, "checkNumberEquals.9");
    checkEquals(x, x, "checkNumberEquals.10");
  }


  private static void checkFromBigInteger()
  {
    // 0
    Number x = Number.fromBigInteger(BigInteger.ZERO);
    Number y = Number.ZERO;
    checkEquals(x, y, "checkFromBigInteger.1");

    // 1
    x = Number.fromBigInteger(BigInteger.ONE);
    y = Number.ONE;
    checkEquals(x, y, "checkFromBigInteger.2");

    // signed random
    x = _signedRandom(256);
    y = Number.fromBigInteger(x.toBigInteger());
    checkEquals(x, y, "checkFromBigInteger.3");
  }


  private static void checkToBigInteger()
  {
    // 0
    BigInteger n = Number.ZERO.toBigInteger();
    BigInteger m = BigInteger.ZERO;
    checkEquals(n, m, "checkToBigInteger.1");

    // 1
    n = Number.ONE.toBigInteger();
    m = BigInteger.ONE;
    checkEquals(n, m, "checkToBigInteger.2");

    // random
    Number x = _signedRandom(256);
    n = x.toBigInteger();
    m = new BigInteger(x.signum(), x.toBytes(32));
    checkEquals(n, m, "checkToBigInteger.3");
  }

  private static void checkBitLength()
  {
    // 0
    int check1 = Number.ZERO.bitLength();
    checkEquals(check1, 0, "checkBitLength.1");

    // 1
    check1 = Number.ONE.bitLength();
    checkEquals(check1, 1, "checkBitLength.2");

    // -1
    check1 = Number.ONE.negate().bitLength();
    checkEquals(check1, 1, "checkBitLength.3");

    // 2
    Number _2 = Number.ONE.add(Number.ONE);
    check1 = _2.bitLength();
    checkEquals(check1, 2, "checkBitLength.4");

    // -2
    check1 = _2.negate().bitLength();
    checkEquals(check1, 2, "checkBitLength.5");

    // 4
    Number _4 = _2.mul(_2);
    check1 = _4.bitLength();
    checkEquals(check1, 3, "checkBitLength.6");
    
    // -4
    check1 = _4.negate().bitLength();
    checkEquals(check1, 3, "checkBitLength.7");

    // 16
    Number _16 = _4.mul(_4);
    check1 = _16.bitLength();
    checkEquals(check1, 5, "checkBitLength.8");

    // -16
    check1 = _16.negate().bitLength();
    checkEquals(check1, 5, "checkBitLength.9");

    // 256
    Number _256 = _16.mul(_16);
    check1 = _256.bitLength();
    checkEquals(check1, 9, "checkBitLength.10");

    // -256
    check1 = _256.negate().bitLength();
    checkEquals(check1, 9, "checkBitLength.11");

    // +- 2^256
    byte[] bytes = new byte[33];
    bytes[0] = (byte) 0x01;
    Number x = Number.fromBytes(1, bytes);
    Number y = Number.fromBytes(-1, bytes);
    checkEquals(x.bitLength(), 257, "checkBitLength.12");
    checkEquals(y.bitLength(), 257, "checkBitLength.13");
  }
}
