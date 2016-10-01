import java.math.BigInteger;
import java.util.Random;

public class Ring2 extends Ring 
{
  @Override public Number zero(){ return Number2.ZERO; }
  @Override public Number one(){ return Number2.ONE; }
  @Override public Number fromBytes(int signum, byte[] val){
    return new Number2(new BigInteger(signum, val));}
  @Override public Number random(int numBits, Random rnd){
    return new Number2(new BigInteger(numBits, rnd));}


}
