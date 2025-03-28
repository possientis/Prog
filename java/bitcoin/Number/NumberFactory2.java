import java.math.BigInteger;
import java.util.Random;

public class NumberFactory2 extends NumberFactory
{
  @Override public Number zero(){ return Number2.ZERO; }
  @Override public Number one(){ return Number2.ONE; }
  @Override public Number fromBytes(int signum, byte[] val){
    return new Number2(new BigInteger(signum, val));}
  @Override public Number random(int numBits, Random rnd){
    return new Number2(new BigInteger(numBits, rnd));}
  @Override public Number fromBigInteger(BigInteger n){
    return new Number2(n);}


}
