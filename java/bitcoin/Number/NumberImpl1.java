import java.math.BigInteger;

public class NumberImpl1 extends Number
{
  // data
  private final BigInteger  value;

  // constructor
  public NumberImpl1(BigInteger value){ this.value = value; }

  public static Number ZERO = new NumberImpl1(BigInteger.ZERO);

  public static Number ONE = new NumberImpl1(BigInteger.ONE);

  public static Number ERROR = null;

  @Override public Number add(Number rhs)
  {
    if(this.isError() || rhs.isError()) return ERROR;
    if(this.getClass() != rhs.getClass()) return ERROR;
    NumberImpl1 cast = (NumberImpl1) rhs;
    return new NumberImpl1(value.add(cast.value));
  }

  @Override public Number mul(Number rhs)
  {
    if(this.isError() || rhs.isError()) return ERROR;
    if(this.getClass() != rhs.getClass()) return ERROR;
    NumberImpl1 cast = (NumberImpl1) rhs;
    return new NumberImpl1(value.multiply(cast.value));
  }

  @Override public boolean isError(){ return this == null; }

  @Override public String toString()
  {
    return isError() ? "Number.ERROR" : value.toString();
  }

}

