public class NumberFactory2 extends NumberFactory
{
  public Number getOne()
  {
    return new Number(NumberImpl2.ONE);
  }

}
