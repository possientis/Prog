import java.util.Random;
import java.security.SecureRandom;

public abstract class Number implements Comparable<Number> {

  // choose implementation of Number and Random
  private static final NumberFactory _factory = new NumberFactory2();
  private static final Random _rnd = new SecureRandom();

  // static factory functions
 
  public static Number ZERO = _factory.zero();
  public static Number ONE = _factory.one();
  public static Number fromBytes(int signum, byte[] val)  // big-endian
  {
    return _factory.fromBytes(signum, val);
  }
  public static Number random(int numBits)
  {
    return _factory.random(numBits, _rnd);
  }


  // instance nembers
  
  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);
  public abstract Number negate();
  public abstract byte[] toBytes(int numBytes); // unsigned, big-endian
  public abstract int signum();                 // 1, 0, -1


  @Override public abstract String toString();
  @Override public abstract int compareTo(Number rhs);
  @Override public abstract int hashCode();
  @Override public boolean equals(Object rhs)
  { 
      return getClass() == rhs.getClass() ? compareTo((Number) rhs) == 0 : false;
  }
}

