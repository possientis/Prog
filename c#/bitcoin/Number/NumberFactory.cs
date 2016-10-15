using System;
using System.Numerics;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public abstract class NumberFactory {
  public abstract Number Zero();
  public abstract Number One();
  public abstract Number FromBytes(int sign, byte[] val); // input big-endian
  public abstract Number Random(int numBits, Random rnd); // uniform
  public abstract Number FromBigInteger(BigInteger n);      
}
