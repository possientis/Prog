using System;
using System.Numerics;

public class Test_Number : Test_Abstract
{
  public static void Main(string[] args)
  {
    Test_Abstract test = new Test_Number();
    test.Run();
  }

  public override void Run()
  {
    LogMessage("Number unit test running ...");
    CheckZERO();
    CheckONE();
    CheckFromBytes();
    CheckSign();
    CheckToBytes();
    CheckRandom();
    CheckAdd();
    CheckMul();
    CheckToString();
    CheckCompareTo();
    CheckHashCode();
    CheckNumberEquals();  
    CheckFromBigInteger();
    CheckToBigInteger();
    CheckBitLength();
  }

  private static Number _SignedRandom(int numBits)
  {
    Number x = Number.Random(numBits);
    Number flip = Number.Random(1);
    return flip.Equals(Number.ONE) ? x.Negate() : x;
  }
 
  private static void CheckZERO()
  {
    Number zero = Number.ZERO;
    Number x = Number.Random(256);
    Number y = zero.Add(x);
    Number z = x.Add(zero);
    CheckEquals(x, y, "CheckZERO.1");
    CheckEquals(x, z, "CheckZERO.2");
  }

  private static void CheckONE()
  {
    Number one = Number.ONE;
    Number x = Number.Random(256);
    Number y = one.Mul(x);
    Number z = x.Mul(one);
    CheckEquals(x, y, "CheckONE.1");
    CheckEquals(x, z, "CheckONE.2");
  }

  private static void CheckFromBytes()
  {
    Number x, y, z, t;
    string eName = "ArgumentException";
    
    // empty array
    byte [] b0 = {};
    x = Number.FromBytes(1, b0);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.1");
    x = Number.FromBytes(-1, b0);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.2");
    x = Number.FromBytes(0, b0);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.3");
    CheckException(() => Number.FromBytes(2,b0), eName, "CheckFromBytes.4");
    CheckException(() => Number.FromBytes(-2,b0), eName, "CheckFromBytes.5");

    // single 0x00 byte
    byte[] b1 = { (byte) 0x00 };
    x = Number.FromBytes(1, b1);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.6");
    x = Number.FromBytes(-1, b1);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.7");
    x = Number.FromBytes(0, b1);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.8");
    CheckException(() => Number.FromBytes(2,b1), eName, "CheckFromBytes.9");
    CheckException(() => Number.FromBytes(-2,b1), eName, "CheckFromBytes.10");

    // two 0x00 bytes
    byte[] b2 = { (byte) 0x00, (byte) 0x00 };
    x = Number.FromBytes(1, b2);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.11");
    x = Number.FromBytes(-1, b2);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.12");
    x = Number.FromBytes(0, b2);
    CheckEquals(x, Number.ZERO, "CheckFromBytes.13");
    CheckException(() => Number.FromBytes(2,b2), eName, "CheckFromBytes.14");
    CheckException(() => Number.FromBytes(-2,b2), eName, "CheckFromBytes.15");

    // single 0x01 byte
    byte[] b3 = { (byte) 0x01 };
    x = Number.FromBytes(1, b3);
    CheckEquals(x, Number.ONE, "CheckFromBytes.16");
    CheckException(() => Number.FromBytes(0, b3), eName, "CheckFromBytes.17");

    // x + (-x) = 0
    byte[] b4 = GetRandomBytes(32); 
    x = Number.FromBytes(1, b4);
    y = Number.FromBytes(-1, b4);
    z = x.Add(y);
    CheckEquals(z, Number.ZERO, "CheckFromBytes.18");

    // multiplying by -1
    z = Number.FromBytes(-1, b3); // -1
    z = z.Mul(x);
    CheckEquals(y, z, "CheckFromBytes.19");

    // padding with 0x00 bytes
    byte[] b5 = GetRandomBytes(28);
    x = Number.FromBytes(1, b5);
    y = Number.FromBytes(-1, b5);
    byte[] b6 = new byte[32];
    b6[0] = (byte) 0x00;
    b6[1] = (byte) 0x00;
    b6[2] = (byte) 0x00;
    b6[3] = (byte) 0x00;
    Array.Copy(b5, 0, b6, 4, 28);
    z = Number.FromBytes(1, b6);
    CheckEquals(x, z, "CheckFromBytes.20");
    z = Number.FromBytes(-1, b6);
    CheckEquals(y, z, "CheckFromBytes.21");
    
    // actual replication
    byte[] b7 = GetRandomBytes(32);
    byte[] b8 = new byte[1];
    b8[0] = (byte) 0xFF;
    Number _256 = Number.FromBytes(1, b8).Add(Number.ONE);
    x = Number.FromBytes(1, b7);
    y = Number.FromBytes(-1, b7);
    z = Number.ZERO;
    t = Number.ZERO;
    for(int i = 0; i < 32; ++i)
    { 
      b8[0] = b7[i];
      z = z.Mul(_256).Add(Number.FromBytes(1, b8)); // z = z*256 + b7[i]
      t = t.Mul(_256).Add(Number.FromBytes(-1,b8)); // t = t*256 - b7[i]
    }
    CheckEquals(x, z, "CheckFromBytes.22");
    CheckEquals(y, t, "CheckFromBytes.23");

    // using ToBytes and Sign
    byte[] b9 = GetRandomBytes(32);
    x = Number.FromBytes(1, b9);
    y = Number.FromBytes(-1, b9);

    CheckEquals(x.Sign, 1, "CheckFromBytes.24");
    CheckEquals(y.Sign, -1, "CheckFromBytes.25");

    byte[] b10 = x.ToBytes(32);
    byte[] b11 = y.ToBytes(32);

    CheckArrayEquals(b9, b10, "CheckFromBytes.26");
    CheckArrayEquals(b9, b11, "CheckFromBytes.27");
  }

  private static void CheckSign()
  {
    CheckEquals(Number.ZERO.Sign, 0, "CheckSign.1");

    byte[] b = GetRandomBytes(32);
    Number x = Number.FromBytes(1, b);
    Number y = Number.FromBytes(-1, b);

    CheckEquals(x.Sign, 1, "CheckSign.2");
    CheckEquals(y.Sign, -1, "CheckSign.3");
  }

  private static void CheckToBytes()
  {
    string eName = "ArithmeticException";
    byte[] bytes;

    // ZERO
    bytes = Number.ZERO.ToBytes(0);
    CheckEquals(bytes.Length, 0, "CheckToBytes.1");

    bytes = Number.ZERO.ToBytes(32);
    CheckEquals(bytes.Length, 32, "CheckToBytes.2");
    for(int i = 0; i < 32; ++i)
    {
      CheckEquals(bytes[i], (byte) 0x00, "CheckToBytes.3");
    }
    
    // ONE
    CheckException(() => Number.ONE.ToBytes(0), eName, "CheckToBytes.4");
    bytes = Number.ONE.ToBytes(1);
    CheckEquals(bytes.Length, 1, "CheckToBytes.5");
    CheckEquals(bytes[0], (byte) 0x01, "CheckToBytes.6");
    bytes = Number.ONE.Negate().ToBytes(1);
    CheckEquals(bytes.Length, 1, "CheckToBytes.7");
    CheckEquals(bytes[0], (byte) 0x01, "CheckToBytes.8");
    bytes = Number.ONE.ToBytes(32);
    CheckEquals(bytes.Length, 32, "CheckToBytes.9");
    CheckEquals(bytes[31], (byte) 0x01, "CheckToBytes.10"); // big-endian
    for(int i = 0; i < 31; ++i)
    {
      CheckEquals(bytes[i], (byte) 0x00, "CheckToBytes.11");
    }

    // random
    Number x = Number.Random(256);
    Number y = x.Negate();
    bytes = x.ToBytes(32);
    CheckEquals(x, Number.FromBytes(1, bytes), "CheckToBytes.12");
    CheckEquals(y, Number.FromBytes(-1, bytes), "CheckToBytes.13");
    bytes = y.ToBytes(32);
    CheckEquals(x, Number.FromBytes(1, bytes), "CheckToBytes.14");
    CheckEquals(y, Number.FromBytes(-1, bytes), "CheckToBytes.15");
  }

  private static void CheckRandom()
  {
    // Checking a random generator should be far more involved
    // than anything done here.

    Number x;
    x = Number.Random(0);
    CheckEquals(x, Number.ZERO, "CheckRandom.1");

    x = Number.Random(1);   // single bit
    CheckCondition(x.Equals(Number.ZERO)||x.Equals(Number.ONE), "CheckRandom.2");

    x = Number.Random(256);
    CheckEquals(x.Sign, 1, "CheckRandom.3");

    int count = 0;
    for(int i = 0; i < 10000; ++i)
    {
      x = Number.Random(256);
      byte[] bytes = x.ToBytes(32);
      
      Number y = Number.Random(5);              // selecting byte 0 to 31
      int index = y.ToBytes(1)[0] & 0xFF;       // 0 to 31
      int test = bytes[index] & 0xFF;
      Number z = Number.Random(3);              // selecting bit 0...7
      int bit = z.ToBytes(1)[0] & 0xFF;         // 0 to 7
      if(((test >> bit) & 0x01) == 1)           // is corresponding bit set? 
      {
        ++count;                                // should be 50% chance occurence
      }
    }

    // should be able to compute upper-bound on probability of failure
    CheckCondition(count > 4800, "CheckRandom.4");
    CheckCondition(count < 5200, "CheckRandom.5");
  }

  private static void CheckAdd()
  {
    Number x = _SignedRandom(256);
    Number y = _SignedRandom(256);
    Number z = _SignedRandom(256);

    // x + 0 = x
    CheckEquals(x.Add(Number.ZERO), x, "CheckAdd.1");

    // 0 + x = x
    CheckEquals(Number.ZERO.Add(x), x, "CheckAdd.2");

    // x + (-x) = 0
    CheckEquals(x.Add(x.Negate()), Number.ZERO, "CheckAdd.3");

    // (-x) + x = 0
    CheckEquals(x.Negate().Add(x), Number.ZERO, "CheckAdd.4");

    // x + y = y + x
    CheckEquals(x.Add(y), y.Add(x), "CheckAdd.5");

    // (x + y) + z = x + (y + z)
    CheckEquals(x.Add(y).Add(z), x.Add(y.Add(z)), "CheckAdd.6");

    // actual Check of x + y
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    BigInteger sum = BigInteger.Add(n,m);
    Number Check = Number.FromBigInteger(sum);
    CheckEquals(Check, x.Add(y), "CheckAdd.7");
  }

  private static void CheckMul()
  {
    Number x = _SignedRandom(256);
    Number y = _SignedRandom(256);
    Number z = _SignedRandom(256);

    // x * 0  = 0
    CheckEquals(x.Mul(Number.ZERO), Number.ZERO, "CheckMul.1");

    // 0 * x = 0
    CheckEquals(Number.ZERO.Mul(x), Number.ZERO, "CheckMul.2");

    // x * 1  = x
    CheckEquals(x.Mul(Number.ONE), x, "CheckMul.3");

    // 1 * x = x
    CheckEquals(Number.ONE.Mul(x), x, "CheckMul.4");

    // (-x) * (-y) = x * y
    CheckEquals(x.Negate().Mul(y.Negate()), x.Mul(y), "CheckMul.5");

    // x * y = y * x
    CheckEquals(x.Mul(y), y.Mul(x), "CheckMul.6");

    // (x * y) * z = x * (y * z)
    CheckEquals(x.Mul(y).Mul(z), x.Mul(y.Mul(z)), "CheckMul.7");
    
    // (x + y) * z = (x * z) + (y * z)
    CheckEquals(x.Add(y).Mul(z), x.Mul(z).Add(y.Mul(z)), "CheckMul.8"); 

    // actual Check of x * y
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    BigInteger prod = BigInteger.Multiply(n, m);
    Number Check = Number.FromBigInteger(prod);
    CheckEquals(Check, x.Mul(y), "CheckMul.9");
  }

  private static void CheckToString()
  {
    string check1;
    string check2;
    Number x;

    // zero
    check1 = Number.ZERO.ToString();
    CheckEquals(check1, "0", "CheckToString.1");

    // one
    check1 = Number.ONE.ToString();
    CheckEquals(check1, "1", "CheckToString.2");

    // random positive
    x = Number.Random(256);
    check1 = x.ToString();
    check2 = x.ToBigInteger().ToString();
    CheckEquals(check1, check2, "CheckToString.2");
  }

  private static void CheckCompareTo()
  {
    // from Random
    Number x = Number.Random(256);  
    Number y = x.Negate();

    CheckEquals(x.CompareTo(Number.ZERO), 1, "CheckCompareTo.1");
    CheckEquals(Number.ZERO.CompareTo(x), -1, "CheckCompareTo.2");
    CheckEquals(y.CompareTo(Number.ZERO), -1, "CheckCompareTo.3");
    CheckEquals(Number.ZERO.CompareTo(y), 1, "CheckCompareTo.4");

    // from bytes
    byte[] bytes = GetRandomBytes(32);
    x = Number.FromBytes(1, bytes);
    y = Number.FromBytes(-1, bytes);

    CheckEquals(x.CompareTo(Number.ZERO), 1, "CheckCompareTo.5");
    CheckEquals(Number.ZERO.CompareTo(x), -1, "CheckCompareTo.6");
    CheckEquals(y.CompareTo(Number.ZERO), -1, "CheckCompareTo.7");
    CheckEquals(Number.ZERO.CompareTo(y), 1, "CheckCompareTo.8");

    // from _signedRandom
    x = _SignedRandom(256);
    y = _SignedRandom(256);

    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();

    CheckEquals(x.CompareTo(y), n.CompareTo(m), "CheckCompareTo.9");
    CheckEquals(y.CompareTo(x), m.CompareTo(n), "CheckCompareTo.10");


    y = Number.FromBigInteger(n);
    CheckEquals(x.CompareTo(y), 0, "CheckCompareTo.11");
    CheckEquals(y.CompareTo(x), 0, "CheckCompareTo.12");

    // 0 <= 1
    CheckEquals(Number.ZERO.CompareTo(Number.ONE), -1, "CheckCompareTo.13");
    CheckEquals(Number.ONE.CompareTo(Number.ZERO), 1, "CheckCompareTo.14");
  }

  private static void CheckHashCode()
  {
    // 0 and 1
    int hash1 = Number.ZERO.GetHashCode();
    int hash2 = Number.ONE.GetHashCode();

    CheckCondition(hash1 != hash2, "CheckHashCode.1");

    // x and - x
    Number x = _SignedRandom(256);
    hash1 = x.GetHashCode();
    hash2 = x.Negate().GetHashCode();
    CheckCondition(hash1 != hash2, "CheckHashCode.2");
    
    // same number
    BigInteger n = x.ToBigInteger();
    Number y = Number.FromBigInteger(n);
    hash1 = x.GetHashCode();
    hash2 = y.GetHashCode();
    CheckEquals(hash1, hash2, "CheckHashCode.3");
  }

  private static void CheckNumberEquals()
  {
    // 0 and 1
    CheckCondition(!Number.ZERO.Equals(Number.ONE), "CheckNumberEquals.1");
    CheckCondition(!Number.ONE.Equals(Number.ZERO), "CheckNumberEquals.2");

    // and and -x
    Number x = _SignedRandom(256);
    CheckCondition(!x.Equals(x.Negate()), "CheckNumberEquals.3");
    CheckCondition(!x.Negate().Equals(x), "CheckNumberEquals.4");

    // same number
    BigInteger n = x.ToBigInteger();
    Number y = Number.FromBigInteger(n);
    CheckCondition(x.Equals(y), "CheckNumberEquals.5");
    CheckCondition(y.Equals(x), "CheckNumberEquals.6");
    CheckCondition(x.Equals(x), "CheckNumberEquals.7");
    CheckEquals(x, y, "CheckNumberEquals.8");
    CheckEquals(y, x, "CheckNumberEquals.9");
    CheckEquals(x, x, "CheckNumberEquals.10");
  }

  private static void CheckFromBigInteger()
  {
    // 0
    Number x = Number.FromBigInteger(BigInteger.Zero);
    Number y = Number.ZERO;
    CheckEquals(x, y, "CheckFromBigInteger.1");

    // 1
    x = Number.FromBigInteger(BigInteger.One);
    y = Number.ONE;
    CheckEquals(x, y, "CheckFromBigInteger.2");

    // signed random
    x = _SignedRandom(256);
    y = Number.FromBigInteger(x.ToBigInteger());
    CheckEquals(x, y, "CheckFromBigInteger.3");
  }

  private static void CheckToBigInteger()
  {
    // 0
    BigInteger n = Number.ZERO.ToBigInteger();
    BigInteger m = BigInteger.Zero;
    CheckEquals(n, m, "CheckToBigInteger.1");

    // 1
    n = Number.ONE.ToBigInteger();
    m = BigInteger.One;
    CheckEquals(n, m, "CheckToBigInteger.2");

    // random
    Number x = _SignedRandom(256);
    n = x.ToBigInteger();

    byte[] bytes = x.ToBytes(33);   // big-endian, 33 -> leading byte is 0x00

    Array.Reverse(bytes);       // now little-endian

    m = new BigInteger(bytes);  // expects two's complement little-endian

    m = (x.Sign == 1) ? m : BigInteger.Negate(m);

    CheckEquals(n, m, "CheckToBigInteger.3");
  }

  private static void CheckBitLength()
  {
    // 0
    int check1 = Number.ZERO.BitLength();
    CheckEquals(check1, 0, "CheckBitLength.1");

    // 1
    check1 = Number.ONE.BitLength();
    CheckEquals(check1, 1, "CheckBitLength.2");

    // -1
    check1 = Number.ONE.Negate().BitLength();
    CheckEquals(check1, 1, "CheckBitLength.3");

    // 2
    Number _2 = Number.ONE.Add(Number.ONE);
    check1 = _2.BitLength();
    CheckEquals(check1, 2, "CheckBitLength.4");

    // -2
    check1 = _2.Negate().BitLength();
    CheckEquals(check1, 2, "CheckBitLength.5");

    // 4
    Number _4 = _2.Mul(_2);
    check1 = _4.BitLength();
    CheckEquals(check1, 3, "CheckBitLength.6");
    
    // -4
    check1 = _4.Negate().BitLength();
    CheckEquals(check1, 3, "CheckBitLength.7");

    // 16
    Number _16 = _4.Mul(_4);
    check1 = _16.BitLength();
    CheckEquals(check1, 5, "CheckBitLength.8");

    // -16
    check1 = _16.Negate().BitLength();
    CheckEquals(check1, 5, "CheckBitLength.9");

    // 256
    Number _256 = _16.Mul(_16);
    check1 = _256.BitLength();
    CheckEquals(check1, 9, "CheckBitLength.10");

    // -256
    check1 = _256.Negate().BitLength();
    CheckEquals(check1, 9, "CheckBitLength.10");

    // +- 2*256
    byte[] bytes = new byte[33];
    bytes[0] = (byte) 0x01;
    Number x = Number.FromBytes(1, bytes);
    Number y = Number.FromBytes(-1, bytes);
    CheckEquals(x.BitLength(), 257, "CheckBitLength.11");
    CheckEquals(y.BitLength(), 257, "CheckBitLength.12");
  }

}

