public class Test 
{
  public static void main(String[] args)
  {
    Ring ring = new Ring1();

    Number zero = ring.zero();
    Number one = ring.one();
    Number two = one.add(one);
    Number four = two.mul(two);

    System.out.println("zero = " + zero);
    System.out.println("one  = " + one);
    System.out.println("two  = " + two);
    System.out.println("four = " + four);

  }
}
