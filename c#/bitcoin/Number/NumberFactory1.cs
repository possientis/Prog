using System;
using System.Numerics;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public class NumberFactory1 : NumberFactory
{
  public override Number Zero(){ return Number1.ZERO; }
  public override Number One(){ return Number1.ONE; }
  public override Number FromBytes(int sign, byte[] val){  // big-endian
    return Number1.FromBytes(sign, val); }
  public override Number Random(int numBits, Random rnd){
    return Number1.Random(numBits, rnd); }
  public override Number FromBigInteger(BigInteger n){
    return new Number1(n);  }
}
