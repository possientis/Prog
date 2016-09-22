public class NumberFactory1 extends NumberFactory
{
  public Number getOne()
  {
    return new Number(NumberImpl1.ONE);
  }

}
