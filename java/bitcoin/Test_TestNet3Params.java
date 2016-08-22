import org.bitcoinj.params.TestNet3Params;

public class Test_TestNet3Params implements Test_Interface {
  public void run(){
    logMessage("TestNet3Params unit test running ...");
    checkTestNet3Params();
    checkCheckDifficultyTransitions();
    checkGet();
    checkGetPaymentProtocolId();
  }

  public void checkTestNet3Params(){
    // only checking constructor can be called succesfully
    // whether object is correctly built should hopefully 
    // follow from the validation of the class public interface
    TestNet3Params test = new TestNet3Params();
    checkNotNull(test, "checkTestNet3Params.1");
  }
 
  public void checkCheckDifficultyTransitions(){/* TODO */}

  // TODO validate against concurrent access
  public void checkGet(){
    TestNet3Params test1 = TestNet3Params.get();
    TestNet3Params test2 = TestNet3Params.get();
    checkEquals(test1, test2, "checkGet.1");
    checkCondition(test1 == test2, "checkGet.2"); // same reference
    TestNet3Params test3 = new TestNet3Params();
    checkEquals(test1, test3, "checkGet.3");
    checkCondition(test1 != test3, "checkGet.4"); // equal, but not same ref
  } 

  public void checkGetPaymentProtocolId(){
    TestNet3Params test = TestNet3Params.get();
    String s1 = TestNet3Params.PAYMENT_PROTOCOL_ID_TESTNET;
    String s2 = test.getPaymentProtocolId();
    checkEquals(s1, s2, "checkGetPaymentProtocolId.1");
    checkEquals(s1,"test", "checkPaymentProtocolId.2");
  }
}
