import org.bitcoinj.params.UnitTestParams;

public class Test_UnitTestParams extends Test_Abstract {
  public void run(){
    logMessage("UnitTestParams unit test running ...");
    checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE();
    checkTESTNET_MAJORITY_REJECT_BLOCK_OUTDATED();
    checkTESTNET_MAJORITY_WINDOW();
    checkUnitTestParams();
    checkGet();
    checkGetPaymentProtocolId();
  }

  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE(){
    int check = UnitTestParams.TESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE;
    checkEquals(check, 4, "checkTESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_REJECT_BLOCK_OUTDATED(){
    int check = UnitTestParams.TESTNET_MAJORITY_REJECT_BLOCK_OUTDATED;
    checkEquals(check, 6, "checkTESTNET_MAJORITY_REJECT_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkTESTNET_MAJORITY_WINDOW(){
    int check = UnitTestParams.UNITNET_MAJORITY_WINDOW;
    checkEquals(check, 8, "checkTESTNET_MAJORITY_WINDOW.1");
  }


  public void checkUnitTestParams(){
    // only checking constructor can be called succesfully
    // whether object is correctly built should hopefully 
    // follow from the validation of the class public interface
    UnitTestParams test = new UnitTestParams();
    checkNotNull(test, "checkUnitTestParams.1");
  }

  // TODO validate against concurrent access
  public void checkGet(){
    UnitTestParams test1 = UnitTestParams.get();
    UnitTestParams test2 = UnitTestParams.get();
    checkEquals(test1, test2, "checkGet.1");
    checkCondition(test1 == test2, "checkGet.2"); // same reference
    UnitTestParams test3 = new UnitTestParams();
    checkEquals(test1, test3, "checkGet.3");
    checkCondition(test1 != test3, "checkGet.4"); // equal, but not same ref
  }

  public void checkGetPaymentProtocolId(){
    UnitTestParams test = UnitTestParams.get();
    String s = test.getPaymentProtocolId();
    checkEquals(s, "unittest", "checkGetPaymentProtocolId.1");
  }
}
