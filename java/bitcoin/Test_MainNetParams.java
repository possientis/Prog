import org.bitcoinj.params.MainNetParams;

public class Test_MainNetParams extends Test_AbstractBitcoinNetParams {

  @Override
  public void run(){
    logMessage("MainNetParams unit test running ...");
    checkMAINNET_MAJORITY_ENFORCE_BLOCK_UPGRADE();
    checkMAINNET_MAJORITY_REJECT_BLOCK_OUTDATED();
    checkMAINNET_MAJORITY_WINDOW();
    checkMainNetParams();
    checkGet();
    checkGetPaymentProtocolId();
  }

  // TODO get independent confirmation of this number
  public void checkMAINNET_MAJORITY_ENFORCE_BLOCK_UPGRADE(){
    int check = MainNetParams.MAINNET_MAJORITY_ENFORCE_BLOCK_UPGRADE;
    checkEquals(check, 750, "checkMAINNET_MAJORITY_ENFORCE_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkMAINNET_MAJORITY_REJECT_BLOCK_OUTDATED(){
    int check = MainNetParams.MAINNET_MAJORITY_REJECT_BLOCK_OUTDATED;
    checkEquals(check, 950, "checkMAINNET_MAJORITY_REJECT_BLOCK_UPGRADE.1");
  }

  // TODO get independent confirmation of this number
  public void checkMAINNET_MAJORITY_WINDOW(){
    int check = MainNetParams.MAINNET_MAJORITY_WINDOW;
    checkEquals(check, 1000, "checkMAINNET_MAJORITY_WINDOW.1");
  }


  public void checkMainNetParams(){
    // only checking constructor can be called successfully
    // whether object is correctly built should hopefully 
    // follow from the validation of the class public interface
    MainNetParams main = new MainNetParams();
    checkNotNull(main, "checkMainNetParams.1");
  }

  // TODO validate against concurrent access
  public void checkGet(){
    MainNetParams main1 = MainNetParams.get();
    MainNetParams main2 = MainNetParams.get();
    checkEquals(main1, main2, "checkGet.1");
    checkCondition(main1 == main2, "checkGet.2"); // same reference
    MainNetParams main3 = new MainNetParams();
    checkEquals(main1, main3, "checkGet.3");
    checkCondition(main1 != main3, "checkGet.4"); // equal, but not same ref
  }

  public void checkGetPaymentProtocolId(){
    MainNetParams main = MainNetParams.get();
    String s1 = MainNetParams.PAYMENT_PROTOCOL_ID_MAINNET;
    String s2 = main.getPaymentProtocolId();
    checkEquals(s1, s2, "checkGetPaymentProtocolId.1");
    checkEquals(s1,"main", "checkPaymentProtocolId.2");
  }
}
