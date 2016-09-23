public class Test 
{
  public static void main(String[] args)
  {
    Ring ring = new RingInteger();

    Number zero = ring.getZero();
    Number one = ring.getOne();
    Number two = one.add(one);
    Number four = two.mul(two);

    System.out.println("zero = " + zero);
    System.out.println("one  = " + one);
    System.out.println("two  = " + two);
    System.out.println("four = " + four);

  }
}
