using System;
using System.Numerics;

public class Bench_Number : Bench_Abstract
{
  public static void Main(string[] args)
  {
    Bench_Abstract bench = new Bench_Number();
    bench.Run();
  }

  public override void Run()
  {
    LogMessage("Number benchmark running ...");

    bool all = true;

    BenchFromBytes();
    BenchToBytes();
    BenchAdd();
    BenchMul();
    BenchToString();
    BenchRandom();

    if(all)
    {
    BenchZERO();
    BenchONE();
    BenchSign();
    BenchCompareTo();
    BenchGetHashCode();
    BenchNumberEquals();  
    BenchFromBigInteger();
    BenchToBigInteger();
    BenchBitLength();
    }
  }

  private static void NOP(Number x){} // used to supress compiler warning
  private static void BenchZERO()
  {
    Benchmark(() => { Number x = Number.ZERO; NOP(x); }, "ZERO", 1000000);
    Benchmark(() => { BigInteger x = BigInteger.Zero; }, "ZERO*", 1000000);
  }
  private static void BenchONE()
  {
    Benchmark(() => { Number x = Number.ONE; NOP(x); }, "ONE", 1000000);
    Benchmark(() => { BigInteger x = BigInteger.One; }, "ONE*", 1000000);
  }
  private static void BenchFromBytes()
  {
    byte[] bytes = GetRandomBytes(32); 

    Benchmark(
        () => { Number.FromBytes(1, bytes); Number.FromBytes(-1, bytes); },
        "FromBytes", 1000000
    );

    // not the same semantics. Hence comparison is not exactly fair
    Benchmark(
        () => { new BigInteger(bytes); new BigInteger(bytes); },
        "FromBytes*", 1000000
    );
  }

  private static void BenchSign()
  {
    Number x = Number.Random(256);
    Number y = x.Negate();
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { int i = x.Sign; i = y.Sign; }, "Sign", 1000000);
    Benchmark(() => { int i = n.Sign; i = m.Sign; }, "Sign*", 1000000);
  }

  private static void BenchToBytes()
  {
    Number x = Number.Random(256);
    Number y = x.Negate();
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => {x.ToBytes(32); y.ToBytes(32); }, "ToBytes", 1000000);
    // cannot really compare as semantics are different. BigInteger's ToByteArray
    // returns a two's complement, little endian encoding and does not have 
    // adjustable size
    Benchmark(() => {n.ToByteArray(); m.ToByteArray(); }, "ToByteArray*", 1000000);
  }

  private static void BenchRandom()
  {
    Benchmark(() => Number.Random(256), "Random (10k)", 10000);
  }

  private static void BenchAdd()
  {
    Number x = Number.Random(256);
    Number y = Number.Random(256).Negate();
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { x.Add(y); y.Add(x); }, "Add", 1000000);
    Benchmark(() => {BigInteger.Add(n, m);BigInteger.Add(m, n);},"Add*",1000000);
  }

  private static void BenchMul()
  {
    Number x = Number.Random(256);
    Number y = Number.Random(256).Negate();
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { x.Mul(y); y.Mul(x); }, "Mul", 1000000);

    Benchmark(
        () => { BigInteger.Multiply(n,m); BigInteger.Multiply(m,n); }, 
        "Mul*", 1000000
    );
  }

  private static void BenchToString()
  {
    Number x = Number.Random(256);
    Number y = x.Negate();
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { x.ToString(); y.ToString(); }, "ToString (10k)", 10000);
    Benchmark(() => { n.ToString(); m.ToString(); }, "ToString* (10k)", 10000);
  }

  private static void BenchCompareTo()
  {
    Number x = Number.Random(256);
    Number y = Number.Random(256);
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { x.CompareTo(y); y.CompareTo(x); }, "CompareTo", 1000000);
    Benchmark(() => { n.CompareTo(m); m.CompareTo(n); }, "CompareTo*", 1000000);
  }

  private static void BenchGetHashCode()
  {
    Number x = Number.Random(256);
    BigInteger n = x.ToBigInteger();
    Benchmark(() => x.GetHashCode(), "GetHashCode", 1000000);
    Benchmark(() => n.GetHashCode(), "GetHashCode*", 1000000);
  }

  private static void BenchNumberEquals()
  {
    Number x = Number.Random(256);
    Number y = Number.Random(256);
    BigInteger n = x.ToBigInteger();
    BigInteger m = y.ToBigInteger();
    Benchmark(() => { x.Equals(y); y.Equals(x); }, "Equals", 1000000);
    Benchmark(() => { n.Equals(m); m.Equals(n); }, "Equals*", 1000000);
  }

  private static void BenchFromBigInteger()
  {
    byte[] bytes = GetRandomBytes(32);
    BigInteger n = new BigInteger(bytes); 
    BigInteger m = BigInteger.Negate(n);
    Benchmark(
        () => { Number.FromBigInteger(n); Number.FromBigInteger(m); },
        "FromBigInteger", 1000000
    );
  }

  private static void BenchToBigInteger()
  {
    Number x = Number.Random(256);
    Number y = x.Negate();
    Benchmark(() => { x.ToBigInteger(); y.ToBigInteger(); }, 
        "ToBigInteger", 1000000
    );
  }

  private static void BenchBitLength()
  {
    Number x = Number.Random(256);
    Benchmark(() => x.BitLength(), "BitLength", 1000000);
  }
}

