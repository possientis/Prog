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

  @Override public Number negate()
  {
    return new Number1(value.negate());
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
    byte[] unsigned;                      // returned byte array
    byte[] signed = value.toByteArray();  // two's complement, big endian
    int signum = value.signum();

    switch(signum)
    {
      case 0:

        unsigned = new byte[numBytes];

        for(int i = 0; i < numBytes; ++i)
        {
          unsigned[i] = 0;
        }

        break;

      case 1:

        unsigned = new byte[numBytes];

        // the signed array may have a leading 0x00 byte to ensure the number
        // is not wrongly interpreted as a negative number. If this is the case
        // then it would be wrong to assume the length of the signed array is
        // the amount of bytes required to encode the magnitude of the number.

        int size;   // number of bytes nedeed to encode magnitude of number
        int start;  // position from which signed array should be copied over

        if((signed[0] & 0xFF) == 0) // signed array has leading 0x00 bytes
        {
          size = signed.length - 1; // required size is one less   
          start = 1;                // copy signed array starting from index 1
        }
        else
        {
          size = signed.length;
          start = 0;
        }

        if(numBytes < size)
        {
          throw new ArithmeticException("numBytes argument is too small");
        }

        // number of leading 0x00 bytes which need to be padded

        int padding = numBytes - size;

        for(int i = 0; i < padding; ++i)
        {
          unsigned[i] = (byte) 0x00;
        }

        // copying signed array over, starting from the correct position 'start'
      
        System.arraycopy(signed, start, unsigned, padding, size);

        break;

      case -1:

        unsigned = negate().toBytes(numBytes); // recursive call

        break;

      default:  // should not happen

        throw new ArithmeticException("Unexpected error");
    }

    return unsigned;
  }

  @Override public int bitLength()
  {
    if(value.compareTo(BigInteger.ZERO) >= 0){
      return value.bitLength();
    }
    else
    {
      return value.negate().bitLength();
    }
  }
}

