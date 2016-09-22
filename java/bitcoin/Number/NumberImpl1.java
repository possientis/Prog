import java.math.BigInteger;

public class NumberImpl1 extends NumberImpl
{
  // data
  private final BigInteger n;

  // main constructor
  private NumberImpl1(BigInteger n){ this.n = n; }
  
  public static final NumberImpl1 ONE = new NumberImpl1(BigInteger.ONE);
}
