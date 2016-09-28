import java.math.BigInteger;

public class Number2 extends Number
{
  // data
  private final BigInteger  value;

  // constructor
  public Number2(BigInteger value){ this.value = value; }

  public static Number ZERO = new Number2(BigInteger.ZERO);
  public static Number ONE = new Number2(BigInteger.ONE);


  @Override public Number add(Number rhs)
  {
    if(rhs == null) throw new NullPointerException("rhs is null");
    if(this.getClass() != rhs.getClass())
    {
      throw new ClassCastException("rhs has illegal type");
    }
    Number2 cast = (Number2) rhs;
    return new Number2(value.add(cast.value));
  }

  @Override public Number mul(Number rhs)
  {
    if(rhs == null) throw new NullPointerException("rhs is null");
    if(this.getClass() != rhs.getClass())
    {
      throw new ClassCastException("rhs has illegal type");
    }
    Number2 cast = (Number2) rhs;
    return new Number2(value.multiply(cast.value));
  }

  @Override public String toString()
  {
    return value.toString();
  }

  @Override public int compareTo(Number rhs)
  {
    if(rhs == null) throw new NullPointerException("rhs is null");
    if(this.getClass() != rhs.getClass())
    {
      throw new ClassCastException("rhs has illegal type");
    }
    Number2 cast = (Number2) rhs;

    return value.compareTo(cast.value);

  }

  @Override public int hashCode()
  {
    return getClass().hashCode() + value.hashCode();
  }

}

