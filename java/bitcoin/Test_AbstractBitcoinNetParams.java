import org.bitcoinj.params.AbstractBitcoinNetParams;
import org.bitcoinj.core.Coin;
import org.bitcoinj.core.Transaction;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.utils.MonetaryFormat;

// AbstractBitcoinNetParams being abstract, cannot be instantiated
// We shall validate the public interface on concrete instance of
// the following subclasses.
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet2Params;
import org.bitcoinj.params.RegTestParams; // derives from TestNet2Params
import org.bitcoinj.params.TestNet3Params;
import org.bitcoinj.params.UnitTestParams;


public class Test_AbstractBitcoinNetParams extends Test_NetworkParameters {
  @Override
  public void run(){
    logMessage("AbstractBitcoinNetParams unit test running ...");
    checkBITCOIN_SCHEME();
    checkCheckDifficultyTransitions();
    checkGetMaxMoney();
    checkMinNonDustOutput();
    checkGetMonetaryFormat();
    checkGetProtocolVersionNum();
    checkGetSerializer();
    checkGetUriScheme();
    checkHasMaxMoney();
    checkIsDifficultyTransitionPoint();
  }

  private final AbstractBitcoinNetParams _params1 = MainNetParams.get();
  private final AbstractBitcoinNetParams _params2 = TestNet2Params.get();
  private final AbstractBitcoinNetParams _params3 = RegTestParams.get();
  private final AbstractBitcoinNetParams _params4 = TestNet3Params.get();
  private final AbstractBitcoinNetParams _params5 = UnitTestParams.get();
 

  public void checkBITCOIN_SCHEME(){
    String check = AbstractBitcoinNetParams.BITCOIN_SCHEME;
    checkEquals(check, "bitcoin", "checkBITCOIN_SCHEME");
  }

  public void checkCheckDifficultyTransitions(){ /* TODO */ }
  public void checkGetMaxMoney(){
    Coin check = AbstractBitcoinNetParams.MAX_MONEY;
    checkEquals(check, _params1.getMaxMoney(), "checkMaxMoney.1");
    checkEquals(check, _params2.getMaxMoney(), "checkMaxMoney.2");
    checkEquals(check, _params3.getMaxMoney(), "checkMaxMoney.3");
    checkEquals(check, _params4.getMaxMoney(), "checkMaxMoney.4");
    checkEquals(check, _params5.getMaxMoney(), "checkMaxMoney.5");
    // arguably redundant, should be caught be NetworkParams validation
    checkEquals(check.toString(), "2100000000000000", "checkMaxMoney.6");
  }

  public void checkMinNonDustOutput(){
    Coin check = Transaction.MIN_NONDUST_OUTPUT;
    checkEquals(check, _params1.getMinNonDustOutput(), "checkMinNonDustOutput.1");
    checkEquals(check, _params2.getMinNonDustOutput(), "checkMinNonDustOutput.2");
    checkEquals(check, _params3.getMinNonDustOutput(), "checkMinNonDustOutput.3");
    checkEquals(check, _params4.getMinNonDustOutput(), "checkMinNonDustOutput.4");
    checkEquals(check, _params5.getMinNonDustOutput(), "checkMinNonDustOutput.5");
    // should be caught by Transaction validation. 2730 satoshis for some reason
    checkEquals(check.toString(), "2730", "checkMinNonDustOutput.6");
  }

  // TODO more checks
  public void checkGetMonetaryFormat(){
    MonetaryFormat format1 = _params1.getMonetaryFormat();
    MonetaryFormat format2 = _params2.getMonetaryFormat();
    MonetaryFormat format3 = _params3.getMonetaryFormat();
    MonetaryFormat format4 = _params4.getMonetaryFormat();
    MonetaryFormat format5 = _params5.getMonetaryFormat();
    checkNotNull(format1, "checkMonetaryFormat.1");
    checkNotNull(format2, "checkMonetaryFormat.2");
    checkNotNull(format3, "checkMonetaryFormat.3");
    checkNotNull(format4, "checkMonetaryFormat.4");
    checkNotNull(format5, "checkMonetaryFormat.5");

  }

  public void checkGetProtocolVersionNum(){

    NetworkParameters.ProtocolVersion[] 
      versions = new NetworkParameters.ProtocolVersion[4];

    versions[0] = NetworkParameters.ProtocolVersion.BLOOM_FILTER;
    versions[1] = NetworkParameters.ProtocolVersion.CURRENT;
    versions[2] = NetworkParameters.ProtocolVersion.MINIMUM;
    versions[3] = NetworkParameters.ProtocolVersion.PONG;

    for(int i = 0; i < 4; ++i){
      int check = versions[i].getBitcoinProtocolVersion();
      int i1 = _params1.getProtocolVersionNum(versions[i]);
      int i2 = _params2.getProtocolVersionNum(versions[i]);
      int i3 = _params3.getProtocolVersionNum(versions[i]);
      int i4 = _params4.getProtocolVersionNum(versions[i]);
      int i5 = _params5.getProtocolVersionNum(versions[i]);
      checkEquals(check, i1, "checkGetProtocolVersionNum.1");
      checkEquals(check, i2, "checkGetProtocolVersionNum.2");
      checkEquals(check, i3, "checkGetProtocolVersionNum.3");
      checkEquals(check, i4, "checkGetProtocolVersionNum.4");
      checkEquals(check, i5, "checkGetProtocolVersionNum.5");
    }

    // should be validated by NetworkParameters.ProtocolVersion
    int bloom = versions[0].getBitcoinProtocolVersion();
    int current = versions[1].getBitcoinProtocolVersion();
    int minimum = versions[2].getBitcoinProtocolVersion();
    int pong = versions[3].getBitcoinProtocolVersion();

    // TODO get independent validation for these numbers
    checkEquals(70000, bloom, "checkGetProtocolVersionNum.6");
    checkEquals(70001, current, "checkGetProtocolVersionNum.7");
    checkEquals(70000, minimum, "checkGetProtocolVersionNum.8");
  }

  public void checkGetSerializer(){ /* TODO */ }

  public void checkGetUriScheme(){
    String scheme = AbstractBitcoinNetParams.BITCOIN_SCHEME;
    checkEquals(scheme, _params1.getUriScheme(), "checkGetUriScheme.1");
    checkEquals(scheme, _params2.getUriScheme(), "checkGetUriScheme.2");
    checkEquals(scheme, _params3.getUriScheme(), "checkGetUriScheme.3");
    checkEquals(scheme, _params4.getUriScheme(), "checkGetUriScheme.4");
    checkEquals(scheme, _params5.getUriScheme(), "checkGetUriScheme.5");
  }

  public void checkHasMaxMoney(){
    checkEquals(true, _params1.hasMaxMoney(), "checkHasMaxMoney.1");
    checkEquals(true, _params2.hasMaxMoney(), "checkHasMaxMoney.2");
    checkEquals(true, _params3.hasMaxMoney(), "checkHasMaxMoney.3");
    checkEquals(true, _params4.hasMaxMoney(), "checkHasMaxMoney.4");
    checkEquals(true, _params5.hasMaxMoney(), "checkHasMaxMoney.5");
  }

  public void checkIsDifficultyTransitionPoint(){ /* TODO */ }
}
