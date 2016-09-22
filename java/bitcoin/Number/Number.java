public class Number
{  
  private static final NumberFactory factory = new NumberFactory2();
  private final NumberImpl value;
  public Number(NumberImpl value) { this.value = value; }

  public static final Number ONE = factory.getOne();

}
