using System;
using System.Numerics;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public class Number1 : Number 
{
  // data
  private readonly BigInteger val;

  // constructor
  public Number1(BigInteger val){ this.val = val; }

  // Unlike java, static members in C# are inherited from the base class.
  // Hence the below declarations hides existing static members of class 
  // 'Number' which generates a compiler warning. The keyword 'new' is
  // required to suppress this warning.

  public new static Number ZERO = new Number1(BigInteger.Zero);

  public new static Number ONE = new Number1(BigInteger.One);

  public new static Number FromBytes(int sign, byte[] val)  // big-endian
  {
    // returning 0

    if(val.Length == 0) return Number1.ZERO;  // sign argument irrelevant 

    if(sign == 0) // checking all bytes are 0x00 for consistency sake
    {
      for(int i = 0; i < val.Length; ++i)
      {
        if(val[i] != (byte) 0x00)
        {
          throw new ArithmeticException("Inconsistent arguments");
        }
      }

      return Number1.ZERO;
    }

    // non-zero output

    byte[] copy = (byte []) val.Clone();

    Array.Reverse(copy);  // 'copy' now little-endian

    // we cannot simply use the array 'copy' to construct a new BigInteger.
    // The issue is that the constructor expects a two's complement 
    // representation of the number. Therefore, if the leading bit of the 
    // leading byte happens to be 1, the BigInteger constructor will assume
    // we are referring to a negative number. To avoid such misinterpretation
    // we need to pad an extra 0x00 byte as a leading byte

    byte lead = copy[copy.Length - 1];

    int mask  = 0x80;       // 1000 0000 in binary

    if((lead & mask) == 1)  // padding is required
    {
      byte[] temp = new byte[copy.Length + 1];

      Array.Copy(copy, 0, temp, 0, copy.Length);

      temp[copy.Length] = (byte) 0x00;  // single leading byte padding

      copy = temp;
    }

    BigInteger n = new BigInteger(copy);

    switch(sign)
    {
      case 1: 

        return new Number1(n);

      case -1:

        return new Number1(BigInteger.Negate(n));

      default:

        throw new ArithmeticException("Illegal sign argument");
    }
 
  }

  // The 'Number' base class has a static method 'Random' which only requires
  // a 'numBits' argument (the random number generator is given as a private
  // field of the class). Therefore, the following static method (which 
  // requires two arguments) is not seen as an override. Hence no 'new' keyword.

  public static Number Random(int numBits, Random rnd)
  {
    // working out required number of bytes
    // 0 bit  -> 0 byte
    // 1 bit  -> 1 byte
    // ...
    // 8 bits -> 1 byte
    // 9 bits -> 2 bytes
    // ...

    int len = (numBits + 7) / 8;

    if(len == 0) return Number1.ZERO;

    byte[] bytes = new byte[len];

    rnd.GetBytes(bytes);  // random number generation 

    // we may have generated too many bits. The leading bits of our big-endian
    // representation needs to be set to 0 so as to reflect numBits exactly. 
    
    int diff = len * 8 - numBits;         // number of leading bits set to 0

    int mask = 0x7f;                      // 0111 1111 in binary

    // we want to regard out 'bytes' array as a big-endian representation,
    // so the leading byte is bytes[0], which is the one needing adjustment
   
    while(diff > 0)
    {
      bytes[0] = (byte) (bytes[0] & mask);  // setting leading byte to 0

      mask = mask >> 1;

      --diff;
    }

    return Number1.FromBytes(1, bytes);
  }

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

    Number1 cast = (Number1) rhs;

    return new Number1(BigInteger.Add(this.val, cast.val));
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

    Number1 cast = (Number1) rhs;

    return new Number1(BigInteger.Multiply(val, cast.val));
}
  
  public override Number Negate()
  {
    return new Number1(BigInteger.Negate(val));
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

    Number1 cast = (Number1) rhs;

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
        
        byte[] signed = val.ToByteArray();  // little-endian

        // note that sign = 1 ensures that signed cannot be the empty array

        Array.Reverse(signed);              // now big-endian 

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
