import org.bitcoinj.params.TestNet2Params;

public class Test_TestNet2Params extends Test_AbstractBitcoinNetParams {

  @Override
  public void run(){
    logMessage("TestNet2Params unit test running ...");
    checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE();
    checkTESTNET_MAJORITY_REJECT_BLOCK_OUTDATED();
    checkTESTNET_MAJORITY_WINDOW();
    checkTestNet2Params();
    checkGet();
    checkGetPaymentProtocolId();
  }
  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE(){
    int check = TestNet2Params.TESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE;
    checkEquals(check, 51, "checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_REJECT_BLOCK_OUTDATED(){
    int check = TestNet2Params.TESTNET_MAJORITY_REJECT_BLOCK_OUTDATED;
    checkEquals(check, 75, "checkTESTNET_MAJORITY_REJECT_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_WINDOW(){
    int check = TestNet2Params.TESTNET_MAJORITY_WINDOW;
    checkEquals(check, 100, "checkTESTNET_MAJORITY_WINDOW.1");
  }


  public void checkTestNet2Params(){
    // only checking constructor can be called successfully
    // whether object is correctly built should hopefully 
    // follow from the validation of the class public interface
    TestNet2Params test = new TestNet2Params();
    checkNotNull(test, "checkTestNet2Params.1");
  }

  // TODO validate against concurrent access
  public void checkGet(){
    TestNet2Params test1 = TestNet2Params.get();
    TestNet2Params test2 = TestNet2Params.get();
    checkEquals(test1, test2, "checkGet.1");
    checkCondition(test1 == test2, "checkGet.2"); // same reference
    TestNet2Params test3 = new TestNet2Params();
    checkEquals(test1, test3, "checkGet.3");
    checkCondition(test1 != test3, "checkGet.4"); // equal, but not same ref
  }

  public void checkGetPaymentProtocolId(){
    TestNet2Params test = TestNet2Params.get();
    String s1 = test.getPaymentProtocolId();
    checkCondition(s1 == null, "checkGetPaymentProtocolId.1");
  }
}

