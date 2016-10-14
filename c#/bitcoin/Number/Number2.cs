using System;
using System.Numerics;

public class Number2 : Number 
{
  // data
  private readonly BigInteger val;

  // constructor
  public Number2(BigInteger val){ this.val = val; }

  // Unlike java, static members in C# are inherited from the base class.
  // Hence the below declarations hides existing static members of class 
  // 'Number' which generates a compiler warning. The keyword 'new' is
  // required to suppress this warning.

  public new static Number ZERO = new Number2(BigInteger.Zero);

  public new static Number ONE = new Number2(BigInteger.One);

  public override Number Add(Number rhs)
  {
    // java NullPointerException
    if(rhs == null) throw new NullReferenceException("rhs is null");

    // java getClass()
    if(this.GetType() != rhs.GetType())
    {
      // java ClassCastException
      throw new InvalidCastException("rhs has illegal type");
    }

    Number2 cast = (Number2) rhs;

    return new Number2(BigInteger.Add(this.val, cast.val));
  }

  public override Number Mul(Number rhs)
  {
    // java NullPointerException
    if(rhs == null) throw new NullReferenceException("rhs is null");

    // java getClass()
    if(this.GetType() != rhs.GetType())
    {
      // java ClassCastException
      throw new InvalidCastException("rhs has illegal type");
    }

    Number2 cast = (Number2) rhs;

    return new Number2(BigInteger.Multiply(val, cast.val));
}
  
  public override Number Negate()
  {
    return new Number2(BigInteger.Negate(val));
  }

  public override string ToString()
  {
    return val.ToString();
  }

  public override int CompareTo(Number rhs)
  {

    // java NullPointerException
    if(rhs == null) throw new NullReferenceException("rhs is null");

    // java getClass()
    if(this.GetType() != rhs.GetType())
    {
      // java ClassCastException
      throw new InvalidCastException("rhs has illegal type");
    }

    Number2 cast = (Number2) rhs;

    return val.CompareTo(cast.val);
  }

  public override int GetHashCode()
  {
    return GetType().GetHashCode() + val.GetHashCode();
  }

  public override int Sign
  {
    get { return val.Sign; }
  }

  public override byte[] ToBytes(int numBytes)
  {
    byte[] unsigned = null; // returned byte array

    int sign = val.Sign;

    switch(sign)
    {
      case 0:

        unsigned = new byte[numBytes];

        for(int i = 0; i < numBytes; ++i)
        {
          unsigned[i] = (byte) 0x00;
        }

        break;

      case 1:

        // Unlike java's 'toByteArray', C# 'ToByteArray' returns a little
        // endian encoding of the number. Both java and C# return a two's 
        // complement representation.
        
        byte[] signedLittleEndian = val.ToByteArray();

        int len = signedLittleEndian.Length;

        byte[] signed = new byte[len];  // big-endian

        int j = len -1 ;

        for(int i = 0; i < len; ++i)
        {
          signed[i] = signedLittleEndian[j]; 
          
          --j;
        }

        unsigned = new byte[numBytes];
        
        // the signed array may have a leading 0x00 byte to ensure the number
        // is not wrongly interpreted as a negative number. If this is the case
        // then it would be wrong to assume the length of the signed array is
        // the amount of bytes required to encode the magnitude of the number.
        
        int size;   // number of bytes needed to encode magnitude of number
        int start;  // position from which signed array should copied over

        // note that sign = 1 ensures that signed cannot be the empty array
        
        if((signed[0] & 0xFF) == 0) // signed array has leading 0x00 byte
        {
          size = signed.Length - 1; // required size is one less
          start = 1;                // copy signed array starting from index 1
        }
        else
        {
          size = signed.Length;
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

        Array.Copy(signed, start, unsigned, padding, size);

        break;

      case -1:

        unsigned = Negate().ToBytes(numBytes);  // recursive call

        break;

      default:  // should not happen

        // java also ArithmeticException
        throw new ArithmeticException("Unexpected error"); 
    }

    return unsigned;
  }

  public override int BitLength()
  {
    if(val.Sign >= 0)
    {
      byte[] bytes = val.ToByteArray();   // little-endian, two's complement

      int len = bytes.Length;

      if(len == 0) return 0;              // number can only be zero

      if((bytes[len - 1] & 0xFF) == 0)    // leading byte is 0x00 to indicate >=0
      {
        --len;
      }

      if(len == 0) return 0;

      int length = 8 * len;               // first estimate

      byte lead = bytes[len - 1];

      int mask = 0x80;                    // 1000 0000 in binary

      while((lead & mask) == 0)           // leading bit is actually 0
      {
        --length;

        mask = mask >> 1;                 // testing next bit to the right
      }

      return length;

    }
    else
    {
      return Negate().BitLength();
    }
  }

  public override BigInteger ToBigInteger()
  {
    return val;
  }
}
