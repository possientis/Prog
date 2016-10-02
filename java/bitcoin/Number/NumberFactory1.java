import java.math.BigInteger;
import java.util.Random;

public class NumberFactory1 extends NumberFactory
{
  @Override public Number zero(){ return Number1.ZERO; }
  @Override public Number one(){ return Number1.ONE; }
  @Override public Number fromBytes(int signum, byte[] val){
    return new Number1(new BigInteger(signum, val));}
  @Override public Number random(int numBits, Random rnd){
    return new Number1(new BigInteger(numBits, rnd));}
}
