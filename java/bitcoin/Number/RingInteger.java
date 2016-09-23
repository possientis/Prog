import java.math.BigInteger;

public class RingInteger extends Ring 
{
  @Override public Number getError(){ return NumberImpl1.ERROR; }
  @Override public Number getZero(){ return NumberImpl1.ZERO; }
  @Override public Number getOne(){ return NumberImpl1.ONE; }
}
