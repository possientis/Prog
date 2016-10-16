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

  private static void CheckRandom(){ /* TODO */ }
  private static void CheckAdd(){ /* TODO */ }
  private static void CheckMul(){ /* TODO */ }
  private static void CheckToString(){ /* TODO */ }
  private static void CheckCompareTo(){ /* TODO */ }
  private static void CheckHashCode(){ /* TODO */ }
  private static void CheckNumberEquals(){ /* TODO */ }
  private static void CheckFromBigInteger(){ /* TODO */ }
  private static void CheckToBigInteger(){ /* TODO */ }
  private static void CheckBitLength(){ /* TODO */ }

}

