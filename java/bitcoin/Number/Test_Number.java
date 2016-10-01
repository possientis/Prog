public class Test_Number extends Test_Abstract
{
  public static void main(String[] args)
  {
    Test_Abstract test = new Test_Number();
    test.run();
  }


  public void run()
  {
    logMessage("Number unit test running ...");
    checkZERO();
    checkONE();
    checkFromBytes();
    checkRandom();
    checkAdd();
    checkMul();
    checkToString();
    checkCompareTo();
    checkHashCode();
    checkNumberEquals();
  }


  private static void checkZERO()
  {
    Number x = Number.ZERO;
  }
  private static void checkONE(){ /* TODO */ }
  private static void checkFromBytes(){ /* TODO */}
  private static void checkRandom(){ /* TODO */}
  private static void checkAdd(){ /* TODO */}
  private static void checkMul(){ /* TODO */ }
  private static void checkToString(){ /* TODO */ }
  private static void checkCompareTo(){ /* TODO */ }
  private static void checkHashCode(){ /* TODO */ }
  private static void checkNumberEquals(){ /* TODO */ }


}
