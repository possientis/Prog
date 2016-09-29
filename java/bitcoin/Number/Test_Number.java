public class Test_Number extends Test_Abstract
{
  public static void main(String[] args)
  {
    // choose implementation here
    Ring ring1 = new Ring1();  
    Ring ring2 = new Ring2();  
      
    Test_Abstract test1 = new Test_Number(ring1);
    Test_Abstract test2 = new Test_Number(ring2);

    test1.run();
    test2.run();

  }

  private final Ring _implementation;
  private final Number ZERO; 
  private final Number ONE; 

  public Test_Number(Ring implementation)
  { 
    checkNotNull(implementation, "Test_Number.1");
    _implementation = implementation; 
    ZERO = _implementation.zero();
    ONE = _implementation.one();
  }

  public void run()
  {
    logMessage("Number unit test running ...");
    checkAdd();
    checkMul();
    checkToString();
    checkCompareTo();
    checkHashCode();
    checkNumberEquals();
  }


  private void checkAdd(){ /* TODO */ }
  private void checkMul(){ /* TODO */ }
  private void checkToString(){ /* TODO */ }
  private void checkCompareTo(){ /* TODO */ }
  private void checkHashCode(){ /* TODO */ }
  private void checkNumberEquals(){ /* TODO */ }


}
