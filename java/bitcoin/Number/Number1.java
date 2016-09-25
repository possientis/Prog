import java.math.BigInteger;

public class Number1 extends Number
{
  // data
  private final BigInteger  value;

  // constructor
  public Number1(BigInteger value){ this.value = value; }

  public static Number ZERO = new Number1(BigInteger.ZERO);

  public static Number ONE = new Number1(BigInteger.ONE);

  public static Number ERROR = null;

  @Override public Number add(Number rhs)
  {
    if(rhs == null) return ERROR;
    if(this.getClass() != rhs.getClass()) return ERROR;
    Number1 cast = (Number1) rhs;
    return new Number1(value.add(cast.value));
  }

  @Override public Number mul(Number rhs)
  {
    if(rhs == null) return ERROR;
    if(this.getClass() != rhs.getClass()) return ERROR;
    Number1 cast = (Number1) rhs;
    return new Number1(value.multiply(cast.value));
  }

  @Override public String toString()
  {
    return (value == null) ? "Number.ERROR" : value.toString();
  }

}

