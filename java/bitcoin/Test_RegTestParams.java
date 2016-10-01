import org.bitcoinj.params.RegTestParams;
import org.bitcoinj.core.Block;

public class Test_RegTestParams extends Test_TestNet2Params {

  @Override
  public void run(){
    logMessage("RegTestParams unit test running ...");
    checkRegTestParams();
    checkAllowEmptyPeerChain();
    checkGet();
    checkGetGenesisBlock();
    checkGetPaymentProtocolId();
  }


  public void checkRegTestParams(){
    // only checking constructor can be succesfully called
    // correctness of built object stems of other public interface validation
    RegTestParams test = new RegTestParams();
    checkNotNull(test, "checkRegTestParams.1");
  }

  public void checkAllowEmptyPeerChain(){
    RegTestParams test = RegTestParams.get();
    checkEquals(true, test.allowEmptyPeerChain(), "checkAllowEmptyPeerChain.1");
  }

  public void checkGet(){
    RegTestParams test1 = RegTestParams.get();
    RegTestParams test2 = RegTestParams.get();
    checkEquals(test1, test2, "checkGet.1");
    checkCondition(test1 == test2, "checkGet.2"); // same reference
    RegTestParams test3 = new RegTestParams();
    checkEquals(test1, test3, "checkGet.3");
    checkCondition(test1 != test3, "checkGet.4");
  }
 
  // TODO more testing on genesis block
  public void checkGetGenesisBlock(){
    RegTestParams test = RegTestParams.get();
    Block block = test.getGenesisBlock();
    String s = "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206";
    String t = block.getHashAsString().toLowerCase();
    checkEquals(s, t, "checkGetGenesisBlock.1");
  }

  public void checkGetPaymentProtocolId(){
    RegTestParams test = RegTestParams.get();
    String s1 = RegTestParams.PAYMENT_PROTOCOL_ID_REGTEST;
    String s2 = test.getPaymentProtocolId();
    checkEquals(s1, s2, "checkGetPaymentProtocolId.1");
    checkEquals(s1,"regtest", "checkPaymentProtocolId.2");
  }
}
