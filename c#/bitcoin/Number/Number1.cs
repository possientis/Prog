using System.Numerics;

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

  public override Number Add(Number rhs)
  {
    return null;  // TODO
  }

  public override Number Mul(Number rhs)
  {
    return null;  // TODO
  }
  
  public override Number Negate()
  {
    return null; // TODO
  }

  public override string ToString()
  {
    return val.ToString();
  }

  public override int CompareTo(Number rhs)
  {
    return 0;     // TODO
  }

  public override int GetHashCode()
  {
    return 0;     // TODO
  }

  public override int Signum()
  {
    return 0;   // TODO
  }

  public override byte[] ToBytes(int numBytes)
  {
    return null;  // TODO
  }

  public override int bitLength()
  {
    return 0;     // TODO
  }

  public override BigInteger ToBigInteger()
  {
    return val;
  }
}
