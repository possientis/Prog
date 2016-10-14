using System;
using System.Numerics;

public class NumberFactory1 : NumberFactory
{
  public override Number Zero(){ return Number1.ZERO; }
  public override Number One(){ return Number1.ONE; }
  public override Number FromBytes(int signum, byte[] val)  // big-endian
  {
    return null; 
  }








  public override Number Random(int numBits, Random rnd){
    return null; /* TODO */ }
  public override Number FromBigInteger(BigInteger n){
    return null; /* TODO */
  }
}
