import java.util.Random;
import java.security.SecureRandom;

public abstract class Number implements Comparable<Number> {

  private static final Ring _ring = new Ring2();          // choose implementation
  private static final Random _rnd = new SecureRandom();  // choose implementation

  // static factory functions
 
  public static Number ZERO = _ring.zero();
  public static Number ONE = _ring.one();
  public static Number fromBytes(int signum, byte[] val)  // big-endian
  {
    return _ring.fromBytes(signum, val);
  }
  public static Number random(int numBits)
  {
    return _ring.random(numBits, _rnd);
  }


  // instance nembers
  
  public abstract Number add(Number rhs);
  public abstract Number mul(Number rhs);


  public abstract String toString();
  public abstract int compareTo(Number rhs);
  public abstract int hashCode();
  public boolean equals(Number rhs){ return compareTo(rhs) == 0; }
}

