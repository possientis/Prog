using System;
using System.Numerics;

public class NumberFactory1 : NumberFactory
{
  public override Number Zero(){ return Number1.ZERO; }
  public override Number One(){ return null; /* TODO */ }
  public override Number FromBytes(int signum, byte[] val){
    return null;  /* TODO */ }
  public override Number Random(int numBits, Random rnd){
    return null; /* TODO */ }
  public override Number FromBigInteger(BigInteger n){
    return null; /* TODO */
  }
}
