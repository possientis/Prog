import java.math.BigInteger;

public class Ring1 extends Ring 
{
  @Override public Number zero(){ return Number1.ZERO; }
  @Override public Number one(){ return Number1.ONE; }
  @Override public Number signedFromBytes(byte[] val){
    return new Number1(new BigInteger(val));}
  @Override public Number unsignedFromBytes(byte[] val){
    return new Number1(new BigInteger(1, val));}
}
