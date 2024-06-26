import java.math.BigInteger;
import java.util.Random;
import java.security.SecureRandom;

public abstract class Number implements Comparable<Number> {

  // choose implementation of Number and Random
  private static final NumberFactory _factory = new NumberFactory1();
  private static final Random _rnd = new SecureRandom();

  // static factory functions
 
  public static Number ZERO = _factory.zero();
  public static Number ONE = _factory.one();
  public static Number fromBytes(int signum, byte[] val)  // big-endian
  {
    return _factory.fromBytes(signum, val);
  }
  public static Number random(int numBits)  // uniform 0 .. 2^(numBits) - 1
  {
    return _factory.random(numBits, _rnd);
  }
  public static Number fromBigInteger(BigInteger n)
  {
    return _factory.fromBigInteger(n);
  }

  // instance members
  
  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);
  public abstract Number negate();
  public abstract byte[] toBytes(int numBytes); // unsigned, big-endian
  public abstract int signum();                 // 1, 0, -1
  public abstract int bitLength();              // number of bits of magnitude
  public abstract BigInteger toBigInteger();

  @Override public abstract String toString();
  @Override public abstract int compareTo(Number rhs);
  @Override public abstract int hashCode();
  @Override public boolean equals(Object rhs)
  { 
      return getClass() == rhs.getClass() ? compareTo((Number) rhs) == 0 : false;
  }
}

