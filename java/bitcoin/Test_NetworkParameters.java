import javax.xml.bind.DatatypeConverter;
import java.util.Arrays;

import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Coin;

// NetworkParameters being abstract, cannot be instantiated
// We shall validate the public interface on concrete instance of
// the following (indirect, via AbstractBitcoinNetParams) subclasses.
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet2Params;
import org.bitcoinj.params.RegTestParams; // derives from TestNet2Params
import org.bitcoinj.params.TestNet3Params;
import org.bitcoinj.params.UnitTestParams;



public class Test_NetworkParameters implements Test_Interface {
  public void run(){
    logMessage("NetworkParameters unit test running ...");
    checkBIP16_ENFORCE_TIME();
    checkID_MAINNET();
    checkID_REGTEST();
    checkID_TESTNET();
    checkID_UNITTESTNET();
    checkINTERVAL();
    checkMAX_COINS();
    checkMAX_MONEY();
    checkPAYMENT_PROTOCOL_ID_MAINNET();
    checkPAYMENT_PROTOCOL_ID_REGTEST();
    checkPAYMENT_PROTOCOL_ID_TESTNET();
    checkPAYMENT_PROTOCOL_ID_UNIT_TESTS();
    checkSATOSHI_KEY();
    checkTARGET_SPACING();
    checkTARGET_TIMESPAN();
    checkAllowEmptyPeerChain();
    checkCheckDifficultyTransitions();
    checkNWPEquals();
    checkFromID();
    checkfromPmtProtocolID();
    checkGetAccetaptableAddressCodes();
    checkGetAddressHeader();
    checkGetAddrSeeds();
    checkGetAlertSigningKey();
    checkGetBip32HeaderPriv();
    checkGetBip32HeaderPub();
    checkGetBlockVerificationFlags();
    checkGetDefaultSerializer();
    checkGetDnsSeeds();
    checkGetDumpedPrivateKeyHeader();
    checkGetGenesisBlock();
    checkGetHttpSeeds();
    checkGetId();
    checkGetInterval();
    checkGetMajorityEnforceBlockUpgrade();
    checkGetMajorityRejectBlockOutdated();
    checkGetMajorityWindow();
    checkGetMaxMoney();
    checkGetMaxTarget();
    checkGetMinNonDustOutput();
    checkGetMonetaryFormat();
    checkGetP2SHHeader();
    checkGetPacketMagic();
    checkGetPaymentProtocolId();
    checkGetPort();
    checkGetProtocolVersionNum();
    checkGetSerializer();
    checkGetSpendableCoinbaseDepth();
    checkGetSubsidyDecreaseBlockCount();
    checkGetTargetTimespan();
    checkGetTransactionVerificationFlags();
    checkGetUriScheme();
    checkHashCode();
    checkHasMaxMoney();
    checkIsCheckpoint();
    checkPassesCheckpoint();
  }

  private final NetworkParameters _params1 = MainNetParams.get();
  private final NetworkParameters _params2 = TestNet2Params.get();
  private final NetworkParameters _params3 = RegTestParams.get();
  private final NetworkParameters _params4 = TestNet3Params.get();
  private final NetworkParameters _params5 = UnitTestParams.get();
 

  public void checkBIP16_ENFORCE_TIME(){
    int check = NetworkParameters.BIP16_ENFORCE_TIME;
    checkEquals(check, 1333238400, "checkBIP16_ENFORCE_TIME");
  }

  public void checkID_MAINNET(){
    String check = NetworkParameters.ID_MAINNET;
    checkEquals(check, "org.bitcoin.production", "checkID_MAINNET.1");
  }

  public void checkID_REGTEST(){
    String check = NetworkParameters.ID_REGTEST;
    checkEquals(check, "org.bitcoin.regtest", "checkID_REGTEST.1");
  }

  public void checkID_TESTNET(){
    String check = NetworkParameters.ID_TESTNET;
    checkEquals(check, "org.bitcoin.test", "checkID_TESTNET.1");
  }

  public void checkID_UNITTESTNET(){
    String check = NetworkParameters.ID_UNITTESTNET;
    checkEquals(check, "org.bitcoinj.unittest", "checkID_UNITTESTNET.1");
  }

  public void checkINTERVAL(){
    // number of blocks between difficulty re-assessment  -> 2016 blocks
    int check1 = NetworkParameters.INTERVAL;
    int check2 = NetworkParameters.TARGET_TIMESPAN
               / NetworkParameters.TARGET_SPACING;
    checkEquals(check1, check2, "checkINTERVAL.1");
  }


  public void checkMAX_COINS(){
    long check = NetworkParameters.MAX_COINS;
    checkEquals(check, 21000000L, "checkMAX_COINS.1");
  }

  public void checkMAX_MONEY(){
    Coin check1 = NetworkParameters.MAX_MONEY;
    Coin check2 = Coin.COIN.multiply(NetworkParameters.MAX_COINS);
    checkEquals(check1, check2, "checkMAX_MONEY.1");
    String check3 = "2100000000000000";  // 2100 trillion satoshis
    checkEquals(check1.toString(), check3, "checkMAX_MONEY.2");
  }

  public void checkPAYMENT_PROTOCOL_ID_MAINNET(){
    String check = NetworkParameters.PAYMENT_PROTOCOL_ID_MAINNET;
    checkEquals(check, "main", "checkPAYMENT_PROTOCOL_ID_MAINNET.1");
  }

  public void checkPAYMENT_PROTOCOL_ID_REGTEST(){
    String check = NetworkParameters.PAYMENT_PROTOCOL_ID_REGTEST;
    checkEquals(check, "regtest", "checkPAYMENT_PROTOCOL_ID_REGTEST.1");
  }

  public void checkPAYMENT_PROTOCOL_ID_TESTNET(){
    String check = NetworkParameters.PAYMENT_PROTOCOL_ID_TESTNET;
    checkEquals(check, "test", "checkPAYMENT_PROTOCOL_ID_TESTNET.1");
  }

  public void checkPAYMENT_PROTOCOL_ID_UNIT_TESTS(){
    String check = NetworkParameters.PAYMENT_PROTOCOL_ID_UNIT_TESTS;
    checkEquals(check, "unittest", "checkPAYMENT_PROTOCOL_ID_UNIT_TESTS.1");
  }

  public void checkSATOSHI_KEY(){
    byte[] check1 = NetworkParameters.SATOSHI_KEY;
    String satoshi = "04" /* uncompressed public key */
       + "fc9702847840aaf195de8442ebecedf5b095cdbb9bc716bda9110971b28a49e0"
       + "ead8564ff0db22209e0374782c093bb899692d524e9d6a6956e7c5ecbcd68284";
    byte[] check2 = DatatypeConverter.parseHexBinary(satoshi);
    checkCondition(Arrays.equals(check1, check2), "checkSATOSHI_KEY.1");
  }


  public void checkTARGET_SPACING(){
    int check1 = NetworkParameters.TARGET_SPACING;
    int check2 = 10 * 60; // 10 minutes
    checkEquals(check1, check2, "checkTARGET_SPACING.1");
  }

  public void checkTARGET_TIMESPAN(){
    int check1 = NetworkParameters.TARGET_TIMESPAN;
    int check2 = 14 * 24 * 60 * 60; // 2 weeks
    checkEquals(check1, check2, "checkTARGET_TIMESPAN.1");
  }

  public void checkAllowEmptyPeerChain(){
    boolean check1 = _params1.allowEmptyPeerChain();
    boolean check2 = _params2.allowEmptyPeerChain();
    boolean check3 = _params3.allowEmptyPeerChain();
    boolean check4 = _params4.allowEmptyPeerChain();
    boolean check5 = _params5.allowEmptyPeerChain();
    checkEquals(check1, true, "checkAllowEmptyPeerChain.1");
    checkEquals(check2, true, "checkAllowEmptyPeerChain.2");
    checkEquals(check3, true, "checkAllowEmptyPeerChain.3");
    checkEquals(check4, true, "checkAllowEmptyPeerChain.4");
    checkEquals(check5, true, "checkAllowEmptyPeerChain.5");
  }

  public void checkCheckDifficultyTransitions(){ /* TODO */ }


  public void checkNWPEquals(){
    NetworkParameters check1 = MainNetParams.get();
    NetworkParameters check2 = TestNet2Params.get();
    NetworkParameters check3 = RegTestParams.get();
    NetworkParameters check4 = TestNet3Params.get();
    NetworkParameters check5 = UnitTestParams.get();
    checkEquals(check1, _params1, "checkNWPEquals.1");
    checkEquals(check2, _params2, "checkNWPEquals.2");
    checkEquals(check3, _params3, "checkNWPEquals.3");
    checkEquals(check4, _params4, "checkNWPEquals.4");
    checkEquals(check5, _params5, "checkNWPEquals.5");
    check1 = new MainNetParams();
    check2 = new TestNet2Params();
    check3 = new RegTestParams();
    check4 = new TestNet3Params();
    check5 = new UnitTestParams();
    checkEquals(check1, _params1, "checkNWPEquals.6");
    checkEquals(check2, _params2, "checkNWPEquals.7");
    checkEquals(check3, _params3, "checkNWPEquals.8");
    checkEquals(check4, _params4, "checkNWPEquals.9");
    checkEquals(check5, _params5, "checkNWPEquals.10");

    // MainNetParams
    checkCondition(!_params1.equals(_params2), "checkNWPEquals.11");
    checkCondition(!_params1.equals(_params3), "checkNWPEquals.12");
    checkCondition(!_params1.equals(_params4), "checkNWPEquals.13");
    checkCondition(!_params1.equals(_params5), "checkNWPEquals.14");
    // TestNet2Params
    checkCondition(!_params2.equals(_params1), "checkNWPEquals.15");
    checkCondition(!_params2.equals(_params3), "checkNWPEquals.16");
    checkCondition(!_params2.equals(_params4), "checkNWPEquals.17");
    checkCondition(!_params2.equals(_params5), "checkNWPEquals.18");
    // RegTestParams (derives from TestNet2Params)
    checkCondition(!_params3.equals(_params1), "checkNWPEquals.19");
    checkCondition(!_params3.equals(_params2), "checkNWPEquals.20");
    checkCondition(!_params3.equals(_params4), "checkNWPEquals.21");
    checkCondition(!_params3.equals(_params5), "checkNWPEquals.22");
    // TestNet3Params (aka TestNet)
    checkCondition(!_params4.equals(_params1), "checkNWPEquals.23");
    checkCondition(!_params4.equals(_params2), "checkNWPEquals.24");
    checkCondition(!_params4.equals(_params3), "checkNWPEquals.25");
    checkCondition(!_params4.equals(_params5), "checkNWPEquals.26");
    // UnitTestParams
    checkCondition(!_params5.equals(_params1), "checkNWPEquals.27");
    checkCondition(!_params5.equals(_params2), "checkNWPEquals.28");
    checkCondition(!_params5.equals(_params3), "checkNWPEquals.29");
    checkCondition(!_params5.equals(_params4), "checkNWPEquals.30");
  }

  public void checkFromID(){
    NetworkParameters check1 = NetworkParameters.fromID(_params1.getId());
    NetworkParameters check2 = NetworkParameters.fromID(_params2.getId());
    NetworkParameters check3 = NetworkParameters.fromID(_params3.getId());
    NetworkParameters check4 = NetworkParameters.fromID(_params4.getId());
    NetworkParameters check5 = NetworkParameters.fromID(_params5.getId());

    checkEquals(check1, _params1, "checkFromID.1");
    logMessage("-> NetworkParameters::fromID see unit test code ...");
//  checkEquals(check2, _params2, "checkFromID.2");
    checkEquals(check3, _params3, "checkFromID.3");
    checkEquals(check4, _params4, "checkFromID.4");
    checkEquals(check5, _params5, "checkFromID.5");
  }

  public void checkfromPmtProtocolID(){
    NetworkParameters check1; 
    NetworkParameters check2; 
    NetworkParameters check3; 
    NetworkParameters check4; 
    NetworkParameters check5; 
    check1 = NetworkParameters.fromPmtProtocolID(_params1.getPaymentProtocolId()); 
//  TestNet2Params object cannot be used like a normal NetworkParameters
//  check2 = NetworkParameters.fromPmtProtocolID(_params2.getPaymentProtocolId());
    check3 = NetworkParameters.fromPmtProtocolID(_params3.getPaymentProtocolId());
    check4 = NetworkParameters.fromPmtProtocolID(_params4.getPaymentProtocolId());
    check5 = NetworkParameters.fromPmtProtocolID(_params5.getPaymentProtocolId());
    logMessage(
        "-> NetworkParameters::fromPmtProtocolID see unit testing code ...");
  }

  public void checkGetAccetaptableAddressCodes(){
    // MainNetParams
    int addressHeader = 0;
    int p2shHeader    = 5;
    int[] check  = _params1.getAcceptableAddressCodes();
    int[] check1 = { addressHeader, p2shHeader };
    checkCondition(Arrays.equals(check, check1), "checkAcceptableAddressCodes.1");
    // TestNet2Params
    addressHeader = 111;
    p2shHeader =  196;
    check = _params2.getAcceptableAddressCodes();
    int[] check2 = { addressHeader, p2shHeader };
    checkCondition(Arrays.equals(check, check2), "checkAcceptableAddressCodes.2");
    // RegTestParams (derives from TestNet2Params)
    check = _params3.getAcceptableAddressCodes();
    int[] check3 = check2;
    checkCondition(Arrays.equals(check, check3), "checkAcceptableAddressCodes.3");
    // TestNet3Params
    check = _params2.getAcceptableAddressCodes();
    int[] check4 = check2;
    checkCondition(Arrays.equals(check, check4), "checkAcceptableAddressCodes.4");
    // UnitTestParams
    check = _params2.getAcceptableAddressCodes();
    int[] check5 = check2;
    checkCondition(Arrays.equals(check, check5), "checkAcceptableAddressCodes.5");
  }

  public void checkGetAddressHeader(){ /* TODO */ }
  public void checkGetAddrSeeds(){ /* TODO */ }
  public void checkGetAlertSigningKey(){ /* TODO */ }
  public void checkGetBip32HeaderPriv(){ /* TODO */ }
  public void checkGetBip32HeaderPub(){ /* TODO */ }
  public void checkGetBlockVerificationFlags(){ /* TODO */ }
  public void checkGetDefaultSerializer(){ /* TODO */ }
  public void checkGetDnsSeeds(){ /* TODO */ }
  public void checkGetDumpedPrivateKeyHeader(){ /* TODO */ }
  public void checkGetGenesisBlock(){ /* TODO */ }
  public void checkGetHttpSeeds(){ /* TODO */ }
  public void checkGetId(){
    String check1 = _params1.getId();
    String check2 = _params2.getId();
    String check3 = _params3.getId();
    String check4 = _params4.getId();
    String check5 = _params5.getId();
    checkEquals(check1, NetworkParameters.ID_MAINNET, "checkGetId.1");
    checkEquals(check2, "org.bitcoin.test", "checkGetId.1");
    checkEquals(check3, NetworkParameters.ID_REGTEST, "checkGetId.3");
    checkEquals(check4, NetworkParameters.ID_TESTNET, "checkGetId.4");
    checkEquals(check5, NetworkParameters.ID_UNITTESTNET, "checkGetId.5");
  }
  public void checkGetInterval(){ /* TODO */ }
  public void checkGetMajorityEnforceBlockUpgrade(){ /* TODO */ }
  public void checkGetMajorityRejectBlockOutdated(){ /* TODO */ }
  public void checkGetMajorityWindow(){ /* TODO */ }
  public void checkGetMaxMoney(){ /* TODO */ }
  public void checkGetMaxTarget(){ /* TODO */ }
  public void checkGetMinNonDustOutput(){ /* TODO */ }
  public void checkGetMonetaryFormat(){ /* TODO */ }
  public void checkGetP2SHHeader(){ /* TODO */ }
  public void checkGetPacketMagic(){ /* TODO */ }
  public void checkGetPaymentProtocolId(){ /* TODO */ }
  public void checkGetPort(){ /* TODO */ }
  public void checkGetProtocolVersionNum(){ /* TODO */ }
  public void checkGetSerializer(){ /* TODO */ }
  public void checkGetSpendableCoinbaseDepth(){ /* TODO */ }
  public void checkGetSubsidyDecreaseBlockCount(){ /* TODO */ }
  public void checkGetTargetTimespan(){ /* TODO */ }
  public void checkGetTransactionVerificationFlags(){ /* TODO */ }
  public void checkGetUriScheme(){ /* TODO */ }
  public void checkHashCode(){ /* TODO */ }
  public void checkHasMaxMoney(){ /* TODO */ }
  public void checkIsCheckpoint(){ /* TODO */ }
  public void checkPassesCheckpoint(){ /* TODO */ }

}
