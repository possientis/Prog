import java.math.BigInteger;

public class Number1 extends Number
{
  // data
  private final BigInteger  value;

  // constructor
  public Number1(BigInteger value){ this.value = value; }

  public static Number ZERO = new Number1(BigInteger.ZERO);
  public static Number ONE = new Number1(BigInteger.ONE);


  @Override public Number add(Number rhs)
  {
    if(rhs == null) throw new NullPointerException("rhs is null");
    if(this.getClass() != rhs.getClass())
    {
      throw new ClassCastException("rhs has illegal type");
    }
    Number1 cast = (Number1) rhs;
    return new Number1(value.add(cast.value));
  }

  @Override public Number mul(Number rhs)
  {
    if(rhs == null) throw new NullPointerException("rhs is null");
    if(this.getClass() != rhs.getClass())
    {
      throw new ClassCastException("rhs has illegal type");
    }
    Number1 cast = (Number1) rhs;
    return new Number1(value.multiply(cast.value));
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
    Number1 cast = (Number1) rhs;

    return value.compareTo(cast.value);

  }

  @Override public int hashCode()
  {
    return getClass().hashCode() + value.hashCode();
  }

  @Override public int signum()
  {
    return value.signum();
  }

  @Override public byte[] toBytes(int numBytes)
  {
    byte[] unsigned = new byte[numBytes];
    byte[] signed = value.toByteArray();  // two's complement, big endian
    int signum = value.signum();

    switch(signum)
    {
      case 0:
        for(int i = 0; i < numBytes; ++i)
        {
          unsigned[i] = 0;
        }

        break;

      case 1:

        // the signed array may have a leading 0x00 byte to ensure the number
        // is not wrongly interpreted as a negative number. If this is the case
        // then it would be wrong to assume the length of the signed array is
        // the amount of bytes required to encode the magnitude of the number.

        if((signed[0] & 0xFF) == 0)
        {
          int size = signed.length - 1;   // needed to encode magnitude

          if(numBytes < size)
          {
            throw new ArithmeticException("numBytes argument is too small");
          }

          int padding = numBytes - size;  // number of leading 0x00 bytes

          for(int i = 0; i < padding; ++i)
          {
            unsigned[i] = (byte) 0x00;
          }

          // copying signed array over, excluding leading 0x00 byte

          System.arraycopy(signed, 1, unsigned, padding, size);
        }
        else
        {
        }

        break;

      case -1:
        break;
      default:  // should not happen
        throw new ArithmeticException("Unexpected error");
    }

    return unsigned;
  }

}

