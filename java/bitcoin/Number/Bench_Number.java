import java.math.BigInteger;

public class Bench_Number extends Bench_Abstract
{
  public static void main(String[] args)
  {
    Bench_Abstract bench = new Bench_Number();
    bench.run();
  }


  public void run()
  {
    logMessage("Number benchmark running ...");

    boolean all = true;

    benchFromBytes();
    benchToBytes();
    benchAdd();
    benchMul();
    benchToString();
    benchRandom();

    if(all)
    {
    benchZERO();
    benchONE();
    benchSignum();
    benchCompareTo();
    benchHashCode();
    benchNumberEquals();  
    benchFromBigInteger();
    benchToBigInteger();
    benchBitLength();
    }
  }


  private static void benchZERO()
  {
    benchmark(() -> { Number x = Number.ZERO; }, "ZERO", 1000000);
    benchmark(() -> { BigInteger x = BigInteger.ZERO; }, "ZERO*", 1000000);
  }

  private static void benchONE()
  {
    benchmark(() -> { Number x = Number.ONE; }, "ONE", 1000000);
    benchmark(() -> { BigInteger x = BigInteger.ONE; }, "ONE*", 1000000);
  }

  private static void benchFromBytes()
  {
    byte[] bytes = getRandomBytes(32); 

    benchmark(
        () -> { Number.fromBytes(1, bytes); Number.fromBytes(-1, bytes); },
        "fromBytes", 1000000
    );

    benchmark(
        () -> { new BigInteger(1, bytes); new BigInteger(-1, bytes); },
        "fromBytes*", 1000000
    );
  }

  private static void benchSignum()
  {
    Number x = Number.random(256);
    Number y = x.negate();
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.signum(); y.signum(); }, "signum", 1000000);
    benchmark(() -> { n.signum(); m.signum(); }, "signum*", 1000000);
  }

  private static void benchToBytes()
  {
    Number x = Number.random(256);
    Number y = x.negate();
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> {x.toBytes(32); y.toBytes(32); }, "toBytes", 1000000);
    // cannot really compare as semantics are different. BigInteger's byteArray
    // returns a two's complement encoding and does not have adjustable size
    benchmark(() -> {n.toByteArray(); m.toByteArray(); }, "toByteArray*", 1000000);
  }

  private static void benchRandom()
  {
    benchmark(() -> Number.random(256), "random (10k)", 10000);
  }

  private static void benchAdd()
  {  
    Number x = Number.random(256);
    Number y = Number.random(256).negate();
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.add(y); y.add(x); }, "add", 1000000);
    benchmark(() -> { n.add(m); m.add(n); }, "add*", 1000000);
  }

  private static void benchMul()
  {
    Number x = Number.random(256);
    Number y = Number.random(256).negate();
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.mul(y); y.mul(x); }, "mul", 1000000);
    benchmark(() -> { n.multiply(m); m.multiply(n); }, "mul*", 1000000);
  }

  private static void benchToString()
  {
    Number x = Number.random(256);
    Number y = x.negate();
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.toString(); y.toString(); }, "toString (10k)", 10000);
    benchmark(() -> { n.toString(); m.toString(); }, "toString* (10k)", 10000);
  }

  private static void benchCompareTo()
  {
    Number x = Number.random(256);
    Number y = Number.random(256);
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.compareTo(y); y.compareTo(x); }, "compareTo", 1000000);
    benchmark(() -> { n.compareTo(m); m.compareTo(n); }, "compareTo*", 1000000);
  }

  private static void benchHashCode()
  {
    Number x = Number.random(256);
    BigInteger n = x.toBigInteger();
    benchmark(() -> x.hashCode(), "hashCode", 1000000);
    benchmark(() -> n.hashCode(), "hashCode*", 1000000);
  }


  private static void benchNumberEquals()
  {
    Number x = Number.random(256);
    Number y = Number.random(256);
    BigInteger n = x.toBigInteger();
    BigInteger m = y.toBigInteger();
    benchmark(() -> { x.equals(y); y.equals(x); }, "equals", 1000000);
    benchmark(() -> { n.equals(m); m.equals(n); }, "equals*", 1000000);
  }

  private static void benchFromBigInteger()
  {
    byte[] bytes = getRandomBytes(32);
    BigInteger n = new BigInteger(1, bytes);
    BigInteger m = new BigInteger(-1, bytes);
    benchmark(
        () -> { Number.fromBigInteger(n); Number.fromBigInteger(m); },
        "fromBigInteger", 1000000
    );
  }

  private static void benchToBigInteger()
  {
    Number x = Number.random(256);
    Number y = x.negate();
    benchmark(() -> { x.toBigInteger(); y.toBigInteger(); }, 
        "toBigInteger", 1000000
    );
  }

  private static void benchBitLength()
  {
    Number x = Number.random(256);
    BigInteger n = x.toBigInteger();
    benchmark(() -> x.bitLength(), "bitLength", 1000000);
    benchmark(() -> n.bitLength(), "bitLength*", 1000000);
  }






}

