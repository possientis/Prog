using System;
using System.Numerics;

public abstract class NumberFactory {
  public abstract Number Zero();
  public abstract Number One();
  public abstract Number FromBytes(int signum, byte[] val); // input big-endian
  public abstract Number Random(int numBits, Random rnd);   // TODO U(0, 2^nb - 1)
  public abstract Number FromBigInteger(BigInteger n);      
}
