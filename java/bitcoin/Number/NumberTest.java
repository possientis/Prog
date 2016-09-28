public class NumberTest
{

  private static final Ring implementation = new Ring1();
  private static final Number ZERO = implementation.zero();
  private static final Number ONE = implementation.one();


  public static void main(String[] args)
  {
    System.err.println("Number unit testing running...");
    checkAdd();
    checkMul();
    checkToString();
    checkCompareTo();
    checkHashCode();
    checkEquals();
    System.err.println("Number unit testing complete.");
  }

  private static void checkAdd(){ /* TODO */ }
  private static void checkMul(){ /* TODO */ }
  private static void checkToString(){ /* TODO */ }
  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkEquals(){ /* TODO */ }


}
