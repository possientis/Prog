using System;
using System.Numerics;

public class NumberFactory2 : NumberFactory
{
  public override Number Zero(){ return Number2.ZERO; }
  public override Number One(){ return Number2.ONE; }

  public override Number FromBytes(int signum, byte[] val){
    return null;  /* TODO */ }
  public override Number Random(int numBits, Random rnd){
    return null; /* TODO */ }
  public override Number FromBigInteger(BigInteger n){
    return null; /* TODO */
  }
}
