using System;
using System.Numerics;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;


public abstract class Number : IComparable<Number> {

  // choose implementation of Number and Random
 
  private static readonly NumberFactory _factory = new NumberFactory1();
  private static readonly Random _rnd = new RNGCryptoServiceProvider();

  // static factory functions

  public static Number ZERO = _factory.Zero();
  public static Number ONE = _factory.One();
  public static Number FromBytes(int sign, byte[] val)  // big-endian
  {
    return _factory.FromBytes(sign, val);
  }
  public static Number Random(int numBits)  // uniform 0 .. 2^(numBits) -1
  {
    return _factory.Random(numBits, _rnd);
  }
  public static Number FromBigInteger(BigInteger n)
  {
    return _factory.FromBigInteger(n);
  }

  // instance members

  public abstract Number Add(Number rhs);
  public abstract Number Mul(Number rhs);
  public abstract Number Negate();
  public abstract byte[] ToBytes(int numBytes); // unsigned, big-endian
  public abstract int Sign { get; }             // 1, 0, -1
  public abstract int BitLength();              // number of bits of magnitude
  public abstract BigInteger ToBigInteger();

  public abstract override string ToString();
  public abstract int CompareTo(Number rhs);    // IComparable<Number>
  public abstract override int GetHashCode();
  public override bool Equals(Object rhs)
  {
    return GetType() == rhs.GetType() ? CompareTo((Number) rhs) == 0 : false;
  }
} 
