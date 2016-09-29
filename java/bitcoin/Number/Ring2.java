import java.math.BigInteger;

public class Ring2 extends Ring 
{
  @Override public Number zero(){ return Number2.ZERO; }
  @Override public Number one(){ return Number2.ONE; }
  @Override public Number signedFromBytes(byte[] val){
    return new Number2(new BigInteger(val));}
  @Override public Number unsignedFromBytes(byte[] val){
    return new Number2(new BigInteger(1, val));}



}
