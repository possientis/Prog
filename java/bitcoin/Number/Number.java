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
  public static Number random(int numBits)
  {
    return _factory.random(numBits, _rnd);
  }


  // instance nembers
  
  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);


  @Override public abstract String toString();
  @Override public abstract int compareTo(Number rhs);
  @Override public abstract int hashCode();
  @Override public boolean equals(Object rhs)
  { 
      return getClass() == rhs.getClass() ? compareTo((Number) rhs) == 0 : false;
  }
}

