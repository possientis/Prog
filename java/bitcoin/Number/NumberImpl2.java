import java.math.BigInteger;

public class NumberImpl2 extends NumberImpl
{
  // data
  private final BigInteger n;

  // main constructor
  private NumberImpl2(BigInteger n){ this.n = n; }
  
  public static final NumberImpl2 ONE = new NumberImpl2(BigInteger.ONE);
}
