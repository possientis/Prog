import java.util.Random;
import java.math.BigInteger;

public abstract class NumberFactory
{
  public abstract Number zero();
  public abstract Number one();
  public abstract Number fromBytes(int signum, byte[] val); // input big-endian
  public abstract Number random(int numBits, Random rnd);   // U(0, 2^nb - 1)
  public abstract Number fromBigInteger(BigInteger n);
}



