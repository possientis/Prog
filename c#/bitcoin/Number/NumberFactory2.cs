using System;
using System.Numerics;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public class NumberFactory2 : NumberFactory
{
  public override Number Zero(){ return Number2.ZERO; }
  public override Number One(){ return Number2.ONE; }
  public override Number FromBytes(int sign, byte[] val){
    return Number2.FromBytes(sign, val); }
  public override Number Random(int numBits, Random rnd){
    return Number2.Random(numBits, rnd); }
  public override Number FromBigInteger(BigInteger n){
    return new Number2(n);  }
}
