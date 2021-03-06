
public class Test 
{
  public static void main(String[] args)
  {
    NumberFactory ring1 = new NumberFactory1();
    NumberFactory ring2 = new NumberFactory2();

    Number zero = ring1.zero();
    Number one = ring1.one();
    Number two = one.add(one);
    Number four = two.mul(two);

    System.out.println("zero = " + zero);
    System.out.println("one  = " + one);
    System.out.println("two  = " + two);
    System.out.println("four = " + four);

    zero = ring2.zero();
    one = ring2.one();
    two = one.add(one);
    four = two.mul(two);

    System.out.println("zero = " + zero);
    System.out.println("one  = " + one);
    System.out.println("two  = " + two);
    System.out.println("four = " + four);

    System.out.println(ring1.zero().hashCode());
    System.out.println(ring2.zero().hashCode());


  }
}
