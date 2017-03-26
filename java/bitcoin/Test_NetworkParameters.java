import javax.xml.bind.DatatypeConverter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.net.URI;
import java.math.BigInteger;


import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Coin;
import org.bitcoinj.core.Block;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.MessageSerializer;
import org.bitcoinj.core.BitcoinSerializer;
import org.bitcoinj.net.discovery.HttpDiscovery;
import org.bitcoinj.core.Utils;
import org.bitcoinj.core.Transaction;
import org.bitcoinj.utils.MonetaryFormat;

import org.bitcoinj.params.AbstractBitcoinNetParams;
// NetworkParameters being abstract, cannot be instantiated
// We shall validate the public interface on concrete instance of
// the following (indirect, via AbstractBitcoinNetParams) subclasses.;
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet2Params;
import org.bitcoinj.params.RegTestParams; // derives from TestNet2Params
import org.bitcoinj.params.TestNet3Params;
import org.bitcoinj.params.UnitTestParams;



public class Test_NetworkParameters extends Test_Abstract {
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

  private static final NetworkParameters _params1 = MainNetParams.get();
  private static final NetworkParameters _params2 = TestNet2Params.get();
  private static final NetworkParameters _params3 = RegTestParams.get();
  private static final NetworkParameters _params4 = TestNet3Params.get();
  private static final NetworkParameters _params5 = UnitTestParams.get();
  private static final String _satoshiKey = "04" /* uncompressed public key */
    + "fc9702847840aaf195de8442ebecedf5b095cdbb9bc716bda9110971b28a49e0"
    + "ead8564ff0db22209e0374782c093bb899692d524e9d6a6956e7c5ecbcd68284";
  private static final String _testNetKey = "04" /* uncompressed public key */
    + "302390343f91cc401d56d68b123028bf52e5fca1939df127f63c6467cdf9c8e2"
    + "c14b61104cf817d0b780da337893ecc4aaff1309e536162dabbdb45200ca2b0a";
  private static final int[] _mainAddrSeeds = {
    0x1ddb1032, 0x6242ce40, 0x52d6a445, 0x2dd7a445, 
    0x8a53cd47, 0x73263750, 0xda23c257, 0xecd4ed57,
    0x0a40ec59, 0x75dce160, 0x7df76791, 0x89370bad, 
    0xa4f214ad, 0x767700ae, 0x638b0418, 0x868a1018,
    0xcd9f332e, 0x0129653e, 0xcc92dc3e, 0x96671640, 
    0x56487e40, 0x5b66f440, 0xb1d01f41, 0xf1dc6041,
    0xc1d12b42, 0x86ba1243, 0x6be4df43, 0x6d4cef43,
    0xd18e0644, 0x1ab0b344, 0x6584a345, 0xe7c1a445,
    0x58cea445, 0xc5daa445, 0x21dda445, 0x3d3b5346,
    0x13e55347, 0x1080d24a, 0x8e611e4b, 0x81518e4b,
    0x6c839e4b, 0xe2ad0a4c, 0xfbbc0a4c, 0x7f5b6e4c,
    0x7244224e, 0x1300554e, 0x20690652, 0x5a48b652,
    0x75c5c752, 0x4335cc54, 0x340fd154, 0x87c07455,
    0x087b2b56, 0x8a133a57, 0xac23c257, 0x70374959,
    0xfb63d45b, 0xb9a1685c, 0x180d765c, 0x674f645d,
    0x04d3495e, 0x1de44b5e, 0x4ee8a362, 0x0ded1b63,
    0xc1b04b6d, 0x8d921581, 0x97b7ea82, 0x1cf83a8e,
    0x91490bad, 0x09dc75ae, 0x9a6d79ae, 0xa26d79ae,
    0x0fd08fae, 0x0f3e3fb2, 0x4f944fb2, 0xcca448b8,
    0x3ecd6ab8, 0xa9d5a5bc, 0x8d0119c1, 0x045997d5,
    0xca019dd9, 0x0d526c4d, 0xabf1ba44, 0x66b1ab55,
    0x1165f462, 0x3ed7cbad, 0xa38fae6e, 0x3bd2cbad,
    0xd36f0547, 0x20df7840, 0x7a337742, 0x549f8e4b,
    0x9062365c, 0xd399f562, 0x2b5274a1, 0x8edfa153,
    0x3bffb347, 0x7074bf58, 0xb74fcbad, 0x5b5a795b,
    0x02fa29ce, 0x5a6738d4, 0xe8a1d23e, 0xef98c445,
    0x4b0f494c, 0xa2bc1e56, 0x7694ad63, 0xa4a800c3,
    0x05fda6cd, 0x9f22175e, 0x364a795b, 0x536285d5,
    0xac44c9d4, 0x0b06254d, 0x150c2fd4, 0x32a50dcc,
    0xfd79ce48, 0xf15cfa53, 0x66c01e60, 0x6bc26661,
    0xc03b47ae, 0x4dda1b81, 0x3285a4c1, 0x883ca96d,
    0x35d60a4c, 0xdae09744, 0x2e314d61, 0x84e247cf,
    0x6c814552, 0x3a1cc658, 0x98d8f382, 0xe584cb5b,
    0x15e86057, 0x7b01504e, 0xd852dd48, 0x56382f56,
    0x0a5df454, 0xa0d18d18, 0x2e89b148, 0xa79c114c,
    0xcbdcd054, 0x5523bc43, 0xa9832640, 0x8a066144,
    0x3894c3bc, 0xab76bf58, 0x6a018ac1, 0xfebf4f43,
    0x2f26c658, 0x31102f4e, 0x85e929d5, 0x2a1c175e,
    0xfc6c2cd1, 0x27b04b6d, 0xdf024650, 0x161748b8,
    0x28be6580, 0x57be6580, 0x1cee677a, 0xaa6bb742,
    0x9a53964b, 0x0a5a2d4d, 0x2434c658, 0x9a494f57,
    0x1ebb0e48, 0xf610b85d, 0x077ecf44, 0x085128bc,
    0x5ba17a18, 0x27ca1b42, 0xf8a00b56, 0xfcd4c257,
    0xcf2fc15e, 0xd897e052, 0x4cada04f, 0x2f35f6d5,
    0x382ce8c9, 0xe523984b, 0x3f946846, 0x60c8be43,
    0x41da6257, 0xde0be142, 0xae8a544b, 0xeff0c254,
    0x1e0f795b, 0xaeb28890, 0xca16acd9, 0x1e47ddd8,
    0x8c8c4829, 0xd27dc747, 0xd53b1663, 0x4096b163,
    0x9c8dd958, 0xcb12f860, 0x9e79305c, 0x40c1a445,
    0x4a90c2bc, 0x2c3a464d, 0x2727f23c, 0x30b04b6d,
    0x59024cb8, 0xa091e6ad, 0x31b04b6d, 0xc29d46a6,
    0x63934fb2, 0xd9224dbe, 0x9f5910d8, 0x7f530a6b,
    0x752e9c95, 0x65453548, 0xa484be46, 0xce5a1b59,
    0x710e0718, 0x46a13d18, 0xdaaf5318, 0xc4a8ff53,
    0x87abaa52, 0xb764cf51, 0xb2025d4a, 0x6d351e41,
    0xc035c33e, 0xa432c162, 0x61ef34ae, 0xd16fddbc,
    0x0870e8c1, 0x3070e8c1, 0x9c71e8c1, 0xa4992363,
    0x85a1f663, 0x4184e559, 0x18d96ed8, 0x17b8dbd5,
    0x60e7cd18, 0xe5ee104c, 0xab17ac62, 0x1e786e1b,
    0x5d23b762, 0xf2388fae, 0x88270360, 0x9e5b3d80,
    0x7da518b2, 0xb5613b45, 0x1ad41f3e, 0xd550854a,
    0x8617e9a9, 0x925b229c, 0xf2e92542, 0x47af0544,
    0x73b5a843, 0xb9b7a0ad, 0x03a748d0, 0x0a6ff862,
    0x6694df62, 0x3bfac948, 0x8e098f4f, 0x746916c3,
    0x02f38e4f, 0x40bb1243, 0x6a54d162, 0x6008414b,
    0xa513794c, 0x514aa343, 0x63781747, 0xdbb6795b,
    0xed065058, 0x42d24b46, 0x1518794c, 0x9b271681,
    0x73e4ffad, 0x0654784f, 0x438dc945, 0x641846a6,
    0x2d1b0944, 0x94b59148, 0x8d369558, 0xa5a97662,
    0x8b705b42, 0xce9204ae, 0x8d584450, 0x2df61555,
    0xeebff943, 0x2e75fb4d, 0x3ef8fc57, 0x9921135e,
    0x8e31042e, 0xb5afad43, 0x89ecedd1, 0x9cfcc047,
    0x8fcd0f4c, 0xbe49f5ad, 0x146a8d45, 0x98669ab8,
    0x98d9175e, 0xd1a8e46d, 0x839a3ab8, 0x40a0016c,
    0x6d27c257, 0x977fffad, 0x7baa5d5d, 0x1213be43,
    0xb167e5a9, 0x640fe8ca, 0xbc9ea655, 0x0f820a4c,
    0x0f097059, 0x69ac957c, 0x366d8453, 0xb1ba2844,
    0x8857f081, 0x70b5be63, 0xc545454b, 0xaf36ded1,
    0xb5a4b052, 0x21f062d1, 0x72ab89b2, 0x74a45318,
    0x8312e6bc, 0xb916965f, 0x8aa7c858, 0xfe7effad,
  };
  private static final String[] mainDnsSeeds = {
    "seed.bitcoin.sipa.be",        // Pieter Wuille
    "dnsseed.bluematt.me",         // Matt Corallo
    "dnsseed.bitcoin.dashjr.org",  // Luke Dashjr
    "seed.bitcoinstats.com",       // Chris Decker
    "seed.bitnodes.io",            // Addy Yeow
    "bitseed.xf2.org",              // Jeff Garzik
    "seed.bitcoin.jonasschnelli.ch" // Jonas Schnelli
  };
  private static final String[] testDnsSeeds = new String[] {
    "testnet-seed.bitcoin.jonasschnelli.ch",  // Jonas Schnelli
    "testnet-seed.bluematt.me",               // Matt Corallo
    "testnet-seed.bitcoin.petertodd.org",     // Peter Todd
    "testnet-seed.bitcoin.schildbach.de"      // Andreas Schildbach
  };


  private static String  _getGenesisBlockHashMain(){
    return "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f";
  }

  private static String _getGenesisBlockHashTest2(){
    return "00000007199508e34a9ff81e6ec0c477a4cccff2a4767a8eee39c11db367b008";
  }

  private static String _getGenesisBlockHashReg(){
    return "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206";
  }

  private static String _getGenesisBlockHashTest3(){
    return "000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943";
  }

  private static String _getAndreasSchildbachPubKey(){
    return "0238746c59d46d5408bf8b1d0af5740fe1a6e1703fcb56b2953f0b965c740d256f";
  }


  private static final HttpDiscovery.Details[] _getHttpSeeds() {
    byte[] pub = DatatypeConverter.parseHexBinary(_getAndreasSchildbachPubKey());
    ECKey key = ECKey.fromPublicOnly(pub);
    URI uri = URI.create("http://httpseed.bitcoin.schildbach.de/peers");
    return new HttpDiscovery.Details[] {
      new HttpDiscovery.Details(key, uri)
    };
  }

  private static final Map<Integer, Sha256Hash> _checkpoints = new HashMap<>();
  private static String _getHash_91722(){
    return "00000000000271a2dc26e7667f8419f2e15416dc6955e5a6c6cdf3f2574dd08e";
  }
  private static String _getHash_91812(){
    return "00000000000af0aed4792b1acee3d966af36cf5def14935db8de83d6f9306f2f";
  }

  private static String _getHash_91842(){
    return "00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec";
  }

  private static String _getHash_91880(){
    return "00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721";
  }

  private static String _getHash_200000(){
    return "000000000000034a7dedef4a161fa058a2d67a173a90155f3a2fe6fc132e0ebf";
  }

  static {
    _checkpoints.put(91722 , Sha256Hash.wrap(_getHash_91722()));
    _checkpoints.put(91812 , Sha256Hash.wrap(_getHash_91812()));
    _checkpoints.put(91842 , Sha256Hash.wrap(_getHash_91842()));
    _checkpoints.put(91880 , Sha256Hash.wrap(_getHash_91880()));
    _checkpoints.put(200000, Sha256Hash.wrap(_getHash_200000()));
  }

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
    byte[] check2 = DatatypeConverter.parseHexBinary(_satoshiKey);
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

  public void checkGetAddressHeader(){
    int check;
    // MainNetParams
    check  = _params1.getAddressHeader();
    checkEquals(check, 0, "checkAddressHeader.1");
    // TestNet2Params
    check  = _params2.getAddressHeader();
    checkEquals(check, 111, "checkAddressHeader.2");
    // RegTestParams
    check  = _params3.getAddressHeader();
    checkEquals(check, 111, "checkAddressHeader.3");
    // TestNet3tParams
    check  = _params4.getAddressHeader();
    checkEquals(check, 111, "checkAddressHeader.4");
    // UnitTestParams
    check  = _params5.getAddressHeader();
    checkEquals(check, 111, "checkAddressHeader.5");
  }

  public void checkGetAddrSeeds(){
    int[] check;
    // MainNetParams
    check = _params1.getAddrSeeds();
    checkCondition(Arrays.equals(check, _mainAddrSeeds), "checkGetAddrSeeds.1");
    // TestNet2Params
    check = _params2.getAddrSeeds();
    checkCondition(check == null, "checkGetAddrSeeds.2");
    // RegTestParams
    check = _params3.getAddrSeeds();
    checkCondition(check == null, "checkGetAddrSeeds.3");
    // TestNet3Params
    check = _params4.getAddrSeeds();
    checkCondition(check == null, "checkGetAddrSeeds.4");
    // UnitTestParams
    check = _params5.getAddrSeeds();
    checkCondition(check == null, "checkGetAddrSeeds.5");
  }

  public void checkGetAlertSigningKey(){
    byte[] main = NetworkParameters.SATOSHI_KEY;
    byte[] test = DatatypeConverter.parseHexBinary(_testNetKey);
    byte[] check1 = _params1.getAlertSigningKey();
    byte[] check2 = _params2.getAlertSigningKey();
    byte[] check3 = _params3.getAlertSigningKey();
    byte[] check4 = _params4.getAlertSigningKey();
    byte[] check5 = _params5.getAlertSigningKey();

    checkCondition(Arrays.equals(main, check1), "checkGetAlertSigningKey.1");
    checkCondition(Arrays.equals(main, check2), "checkGetAlertSigningKey.2");
    checkCondition(Arrays.equals(main, check3), "checkGetAlertSigningKey.3");
    checkCondition(Arrays.equals(test, check4), "checkGetAlertSigningKey.4");
    checkCondition(Arrays.equals(main, check5), "checkGetAlertSigningKey.5");
  }

  public void checkGetBip32HeaderPriv(){
    int check;
    // MaiNetParams
    check = _params1.getBip32HeaderPriv();
    // TODO understand why this number is said to yield 'xprv' in base58 
    checkEquals(check,0x0488ADE4, "checkGetBip32HeaderPriv.1");
    // TestNet2Params
    check = _params2.getBip32HeaderPriv();
    checkEquals(check,0x04358394, "checkGetBip32HeaderPriv.2");
    // RegTestParams
    check = _params3.getBip32HeaderPriv();
    checkEquals(check,0x04358394, "checkGetBip32HeaderPriv.3");
    // TestNet3Params
    check = _params4.getBip32HeaderPriv();
    checkEquals(check,0x04358394, "checkGetBip32HeaderPriv.4");
    // UnitTestParams
    check = _params5.getBip32HeaderPriv();
    checkEquals(check,0x04358394, "checkGetBip32HeaderPriv.5");
  } 

  public void checkGetBip32HeaderPub(){
    int check;
    // MaiNetParams
    check = _params1.getBip32HeaderPub();
    // TODO understand why this number is said to yield 'xpub' in base58 
    checkEquals(check,0x0488B21E, "checkGetBip32HeaderPub.1");
    // TestNet2Params
    check = _params2.getBip32HeaderPub();
    checkEquals(check,0x043587CF, "checkGetBip32HeaderPub.2");
    // RegTestParams
    check = _params3.getBip32HeaderPub();
    checkEquals(check,0x043587CF, "checkGetBip32HeaderPub.3");
    // TestNet3Params
    check = _params4.getBip32HeaderPub();
    checkEquals(check,0x043587CF, "checkGetBip32HeaderPub.4");
    // UnitTestParams
    check = _params5.getBip32HeaderPub();
    checkEquals(check,0x043587CF, "checkGetBip32HeaderPub.5");
  } 

  public void checkGetBlockVerificationFlags(){ /* TODO */ }

  public void checkGetDefaultSerializer(){
    MessageSerializer check;
    BitcoinSerializer bcheck;
    String className = "org.bitcoinj.core.BitcoinSerializer";
    String scheck;

    // This could be replaced by a loop, as nothing is specific to the
    // concrete NetworkParameters subclass. A loop makes diagnostic more
    // difficult in case of failure.

    // MainNetParams
    check = _params1.getDefaultSerializer();
    checkNotNull(check, "checkDefaultSerializer.1");
    scheck = check.getClass().getName();
    checkEquals(scheck, className, "checkDefaultSerializer.2");
    bcheck = (BitcoinSerializer) check;
    checkEquals(_params1, bcheck.getParameters(), "checkDefaultSerializer.3");
    // TestNet2Params
    check = _params2.getDefaultSerializer();
    checkNotNull(check, "checkDefaultSerializer.4");
    scheck = check.getClass().getName();
    checkEquals(scheck, className, "checkDefaultSerializer.5");
    bcheck = (BitcoinSerializer) check;
    checkEquals(_params2, bcheck.getParameters(), "checkDefaultSerializer.6");
    // RegTestParams
    check = _params3.getDefaultSerializer();
    checkNotNull(check, "checkDefaultSerializer.7");
    scheck = check.getClass().getName();
    checkEquals(scheck, className, "checkDefaultSerializer.8");
    bcheck = (BitcoinSerializer) check;
    checkEquals(_params3, bcheck.getParameters(), "checkDefaultSerializer.9");
    // TestNet3Params
    check = _params4.getDefaultSerializer();
    checkNotNull(check, "checkDefaultSerializer.10");
    scheck = check.getClass().getName();
    checkEquals(scheck, className, "checkDefaultSerializer.11");
    bcheck = (BitcoinSerializer) check;
    checkEquals(_params4, bcheck.getParameters(), "checkDefaultSerializer.12");
    // UnitTestParams
    check = _params5.getDefaultSerializer();
    checkNotNull(check, "checkDefaultSerializer.13");
    scheck = check.getClass().getName();
    checkEquals(scheck, className, "checkDefaultSerializer.14");
    bcheck = (BitcoinSerializer) check;
    checkEquals(_params5, bcheck.getParameters(), "checkDefaultSerializer.15");
  }

  public void checkGetDnsSeeds(){
    String[] check;
    // MainNetParams
    check = _params1.getDnsSeeds();
    checkCondition(Arrays.equals(check, mainDnsSeeds), "checkGetDnsSeeds.1");
    // TestNet2Params
    check = _params2.getDnsSeeds();
    checkCondition(check == null, "checkGetDnsSeeds.2");
    // RegTestParams
    check = _params3.getDnsSeeds();
    checkCondition(check == null, "checkGetDnsSeeds.3");
    // TestNet3Params
    check = _params4.getDnsSeeds();
    checkCondition(Arrays.equals(check, testDnsSeeds), "checkGetDnsSeeds.4");
    // UnitTestParams
    check = _params5.getDnsSeeds();
    checkCondition(check == null, "checkGetDnsSeeds.5");
  }
  public void checkGetDumpedPrivateKeyHeader(){
    int check;
    // MainNetParams;
    check = _params1.getDumpedPrivateKeyHeader();
    checkEquals(check, 128, "checkDumpedPrivateKeyHeader.1");
    // TestNet2Params;
    check = _params2.getDumpedPrivateKeyHeader();
    checkEquals(check, 239, "checkDumpedPrivateKeyHeader.2");
    // RegTestParams;
    check = _params3.getDumpedPrivateKeyHeader();
    checkEquals(check, 239, "checkDumpedPrivateKeyHeader.3");
    // TestNet3Params;
    check = _params4.getDumpedPrivateKeyHeader();
    checkEquals(check, 239, "checkDumpedPrivateKeyHeader.4");
    // UnitTestParams;
    check = _params5.getDumpedPrivateKeyHeader();
    checkEquals(check, 239, "checkDumpedPrivateKeyHeader.5");
  }

  public void checkGetGenesisBlock(){
    Block check;
    String s1;
    String s2;
    
    //MainNetParams
    check = _params1.getGenesisBlock();
    s1 = check.getHashAsString();
    s2 = _getGenesisBlockHashMain();
    checkEquals(s1, s2, "checkGetGenesisBlock.1");
    //TestNet2Params
    check = _params2.getGenesisBlock();
    s1 = check.getHashAsString();
    s2 = _getGenesisBlockHashTest2();
    checkEquals(s1, s2, "checkGetGenesisBlock.2");
    //RegTestParams
    check = _params3.getGenesisBlock();
    s1 = check.getHashAsString();
    s2 = _getGenesisBlockHashReg();
    checkEquals(s1, s2, "checkGetGenesisBlock.3");
    //TestNet3Params
    check = _params4.getGenesisBlock();
    s1 = check.getHashAsString();
    s2 = _getGenesisBlockHashTest3();
    checkEquals(s1, s2, "checkGetGenesisBlock.4");
    //UnitTestParams
    check = _params5.getGenesisBlock(); // hash may vary
    long diff1 = Block.EASIEST_DIFFICULTY_TARGET;
    long diff2 = check.getDifficultyTarget();
  }

  public void checkGetHttpSeeds(){
    HttpDiscovery.Details[] check;
    HttpDiscovery.Details[] check2 = _getHttpSeeds();
    ECKey k1;
    ECKey k2;
    URI u1;
    URI u2;
    String s1;
    String s2;

    // MainNetParams
    check = _params1.getHttpSeeds();
    checkEquals(check.length, 1, "checkGetHttpSeeds.1");
    k1 = check[0].pubkey;
    k2 = check2[0].pubkey;
    u1 = check[0].uri;
    u2 = check2[0].uri;
    s1 = k1.getPublicKeyAsHex();
    s2 = k2.getPublicKeyAsHex();
    checkEquals(s1, s2, "checkGetHttpSeeds.2");
    checkEquals(u1, u2, "checkGetHttpSeeds.3");
    // TestNet2Params
    check = _params2.getHttpSeeds();
    checkEquals(check.length, 0, "checkGetHttpSeeds.4");
    // RegTestParams
    check = _params3.getHttpSeeds();
    checkEquals(check.length, 0, "checkGetHttpSeeds.5");
    // TestNet3Params
    check = _params4.getHttpSeeds();
    checkEquals(check.length, 0, "checkGetHttpSeeds.6");
    // UnitTestParams
    check = _params5.getHttpSeeds();
    checkEquals(check.length, 0, "checkGetHttpSeeds.7");
  }

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

  public void checkGetInterval(){
    int check1 = _params1.getInterval();
    int check2 = _params2.getInterval();
    int check3 = _params3.getInterval();
    int check4 = _params4.getInterval();
    int check5 = _params5.getInterval();

    // MainNetParams
    checkEquals(check1, NetworkParameters.INTERVAL, "checkGetInterval.1");
    checkEquals(check2, NetworkParameters.INTERVAL, "checkGetInterval.2");
    checkEquals(check3, 2147483647, "checkGetInterval.3"); // RegTestParams
    checkEquals(check4, NetworkParameters.INTERVAL, "checkGetInterval.4");
    checkEquals(check5, 10, "checkGetInterval.5");    // UnitTestParams
  }

  public void checkGetMajorityEnforceBlockUpgrade(){
    int main = MainNetParams.MAINNET_MAJORITY_ENFORCE_BLOCK_UPGRADE;
    int test = TestNet2Params.TESTNET_MAJORITY_ENFORCE_BLOCK_UPGRADE;

    int check1 = _params1.getMajorityEnforceBlockUpgrade();
    int check2 = _params2.getMajorityEnforceBlockUpgrade();
    int check3 = _params3.getMajorityEnforceBlockUpgrade();
    int check4 = _params4.getMajorityEnforceBlockUpgrade();
    int check5 = _params5.getMajorityEnforceBlockUpgrade();

    checkEquals(check1, main, "checkGetMajorityEnforceBlockUpgrade.1");
    checkEquals(check2, test, "checkGetMajorityEnforceBlockUpgrade.2");
    checkEquals(check3, main, "checkGetMajorityEnforceBlockUpgrade.3");
    checkEquals(check4, test, "checkGetMajorityEnforceBlockUpgrade.4");
    checkEquals(check5, 3, "checkGetMajorityEnforceBlockUpgrade.5");
  }

  public void checkGetMajorityRejectBlockOutdated(){
    int main = MainNetParams.MAINNET_MAJORITY_REJECT_BLOCK_OUTDATED;
    int test = TestNet2Params.TESTNET_MAJORITY_REJECT_BLOCK_OUTDATED;

    int check1 = _params1.getMajorityRejectBlockOutdated();
    int check2 = _params2.getMajorityRejectBlockOutdated();
    int check3 = _params3.getMajorityRejectBlockOutdated();
    int check4 = _params4.getMajorityRejectBlockOutdated();
    int check5 = _params5.getMajorityRejectBlockOutdated();

    checkEquals(check1, main, "checkGetMajorityRejectBlockOutdated.1");
    checkEquals(check2, test, "checkGetMajorityRejectBlockOutdated.2");
    checkEquals(check3, main, "checkGetMajorityRejectBlockOutdated.3");
    checkEquals(check4, test, "checkGetMajorityRejectBlockOutdated.4");
    checkEquals(check5, 4, "checkGetMajorityRejectBlockOutdated.5");
  }

  public void checkGetMajorityWindow(){
    int main = MainNetParams.MAINNET_MAJORITY_WINDOW;
    int test = TestNet2Params.TESTNET_MAJORITY_WINDOW;

    int check1 = _params1.getMajorityWindow();
    int check2 = _params2.getMajorityWindow();
    int check3 = _params3.getMajorityWindow();
    int check4 = _params4.getMajorityWindow();
    int check5 = _params5.getMajorityWindow();

    checkEquals(check1, main, "checkGetMajorityWindow.1");
    checkEquals(check2, test, "checkGetMajorityWindow.2");
    checkEquals(check3, main, "checkGetMajorityWindow.3");
    checkEquals(check4, test, "checkGetMajorityWindow.4");
    checkEquals(check5, 7, "checkGetMajorityWindow.5");
  }

  public void checkGetMaxMoney(){
    Coin check = AbstractBitcoinNetParams.MAX_MONEY;
    Coin check1 = _params1.getMaxMoney();
    Coin check2 = _params2.getMaxMoney();
    Coin check3 = _params3.getMaxMoney();
    Coin check4 = _params4.getMaxMoney();
    Coin check5 = _params5.getMaxMoney();
    checkEquals(check, check1, "checkGetMaxMoney.1");
    checkEquals(check, check2, "checkGetMaxMoney.2");
    checkEquals(check, check3, "checkGetMaxMoney.3");
    checkEquals(check, check4, "checkGetMaxMoney.4");
    checkEquals(check, check5, "checkGetMaxMoney.5");
  }

  public void checkGetMaxTarget(){

    // Easiest allowable proof of work
    BigInteger check1;
    BigInteger check2;
  
    // MainNetParams (28 bytes)
    // ffff0000000000000000000000000000000000000000000000000000
    check1 = Utils.decodeCompactBits(0x1d00ffffL);
    check2 = _params1.getMaxTarget();
    checkEquals(check1, check2, "checkGetMaxTarget.1");

    // TestNet2Params (28 bytes)
    // fffff0000000000000000000000000000000000000000000000000000
    check1 = Utils.decodeCompactBits(0x1d0fffffL);
    check2 = _params2.getMaxTarget();
    checkEquals(check1, check2, "checkGetMaxTarget.2");

    // RegTestParams (33 bytes)
    // 7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    check1 = new BigInteger(
      "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",16);
    check2 = _params3.getMaxTarget();
    checkEquals(check1, check2, "checkGetMaxTarget.3");

    // TestNet3Params (28 bytes)
    // ffff0000000000000000000000000000000000000000000000000000
    check1 = Utils.decodeCompactBits(0x1d00ffffL);
    check2 = _params4.getMaxTarget();
    checkEquals(check1, check2, "checkGetMaxTarget.4");


    // UnitTestParams (33 bytes)
    // "00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    check1 = new BigInteger(
        "00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",16);
    check2 = _params5.getMaxTarget();
    checkEquals(check1, check2, "checkGetMaxTarget.5");
  }

  public void checkGetMinNonDustOutput(){
    // pasted from AbstractBitcoinNetParams
    Coin check = Transaction.MIN_NONDUST_OUTPUT;
    checkEquals(check, _params1.getMinNonDustOutput(), "checkMinNonDustOutput.1");
    checkEquals(check, _params2.getMinNonDustOutput(), "checkMinNonDustOutput.2");
    checkEquals(check, _params3.getMinNonDustOutput(), "checkMinNonDustOutput.3");
    checkEquals(check, _params4.getMinNonDustOutput(), "checkMinNonDustOutput.4");
    checkEquals(check, _params5.getMinNonDustOutput(), "checkMinNonDustOutput.5");
    // should be caught by Transaction validation. 2730 satoshis for some reason
    checkEquals(check.toString(), "2730", "checkMinNonDustOutput.6");
  }

  public void checkGetMonetaryFormat(){
    // pasted from AbstractBitcoinNetParams
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

  public void checkGetP2SHHeader(){
    int check;
    // MainNetParams
    check  = _params1.getP2SHHeader();
    checkEquals(check, 5, "checkP2SHHeader.1");
    // TestNet2Params
    check  = _params2.getP2SHHeader();
    checkEquals(check, 196, "checkP2SHHeader.2");
    // RegTestParams
    check  = _params3.getP2SHHeader();
    checkEquals(check, 196, "checkP2SHHeader.3");
    // TestNet3tParams
    check  = _params4.getP2SHHeader();
    checkEquals(check, 196, "checkP2SHHeader.4");
    // UnitTestParams
    check  = _params5.getP2SHHeader();
    checkEquals(check, 196, "checkP2SHHeader.5");
  }
 
  public void checkGetPacketMagic(){
    // indicates message origin network and is used to seek 
    // to the next message when stream state is unknown
    long check;

    // MainNetParams
    check = _params1.getPacketMagic();
    checkEquals(check, 0xf9beb4d9L, "checkGetPacketMagic.1");

    // TestNet2Params
    check = _params2.getPacketMagic();
    checkEquals(check, 0xfabfb5daL, "checkGetPacketMagic.2");

    // RegTestParams
    check = _params3.getPacketMagic();
    checkEquals(check, 0xfabfb5daL, "checkGetPacketMagic.3");
    
    // TestNet3Params
    check = _params4.getPacketMagic();
    checkEquals(check, 0x0b110907L, "checkGetPacketMagic.4");

    // UnitTestParams
    check = _params5.getPacketMagic();
    checkEquals(check, 0x0b110907L, "checkGetPacketMagic.5");
  }
  public void checkGetPaymentProtocolId(){
    String check;

    // MainNetParams
    check = _params1.getPaymentProtocolId();
    checkEquals(check, "main", "checkPaymentProtocolId.1");

    // TestNet2Params
    check = _params2.getPaymentProtocolId();
    checkCondition(check == null, "checkPaymentProtocolId.2");

    // RegTestParams
    check = _params3.getPaymentProtocolId();
    checkEquals(check, "regtest", "checkPaymentProtocolId.3");

    // TestNet3Params
    check = _params4.getPaymentProtocolId();
    checkEquals(check, "test", "checkPaymentProtocolId.4");

    // UnitTestParams
    check = _params5.getPaymentProtocolId();
    checkEquals(check, "unittest", "checkPaymentProtocolId.5");
  }

  public void checkGetPort(){
    int check;

    // MainNetParams
    check = _params1.getPort();
    checkEquals(check, 8333, "checkGetPort.1");

    // TestNet2Params
    check = _params2.getPort();
    checkEquals(check, 18333, "checkGetPort.2");

    // RegTestParams
    check = _params3.getPort();
    checkEquals(check, 18444, "checkGetPort.3");

    // TestNet3Params
    check = _params4.getPort();
    checkEquals(check, 18333, "checkGetPort.4");

    
    // UnitTestParams
    check = _params5.getPort();
    checkEquals(check, 18333, "checkGetPort.5");
  }
     
  public void checkGetProtocolVersionNum(){
    // pasted from AsbtractBitcoinNetParams
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

  public void checkGetSpendableCoinbaseDepth(){
    // The depth of blocks required for a coinbase transaction to be spendable
    int check;

    // MainNetParams
    check = _params1.getSpendableCoinbaseDepth();
    checkEquals(check, 100, "checkGetSpendableCoinbaseDepth.1");

    // TestNet2Params
    check = _params2.getSpendableCoinbaseDepth();
    checkEquals(check, 100, "checkGetSpendableCoinbaseDepth.2");
    
    // RegTestParams
    check = _params3.getSpendableCoinbaseDepth();
    checkEquals(check, 100, "checkGetSpendableCoinbaseDepth.3");


    // TestNet3Params
    check = _params4.getSpendableCoinbaseDepth();
    checkEquals(check, 100, "checkGetSpendableCoinbaseDepth.4");

    // UnitTestParams
    check = _params5.getSpendableCoinbaseDepth();
    checkEquals(check, 5, "checkGetSpendableCoinbaseDepth.5");

  }

  public void checkGetSubsidyDecreaseBlockCount(){
    int check;

    // MainNetParams
    check = _params1.getSubsidyDecreaseBlockCount();
    checkEquals(check, 210000, "checkGetSubsidyDecreaseBlockCount.1");

    // TestNet2Params
    check = _params2.getSubsidyDecreaseBlockCount();
    checkEquals(check, 210000, "checkGetSubsidyDecreaseBlockCount.2");
    
    // RegTestParams
    check = _params3.getSubsidyDecreaseBlockCount();
    checkEquals(check, 150, "checkGetSubsidyDecreaseBlockCount.3");


    // TestNet3Params
    check = _params4.getSubsidyDecreaseBlockCount();
    checkEquals(check, 210000, "checkGetSubsidyDecreaseBlockCount.4");

    // UnitTestParams
    check = _params5.getSubsidyDecreaseBlockCount();
    checkEquals(check, 100, "checkGetSubsidyDecreaseBlockCount.5");
  }

  public void checkGetTargetTimespan(){
    // how much time in seconds is supposed to pass between "interval" blocks
    // about 2 weeks or 1209600 seconds
    int check;

    // MainNetParams
    check = _params1.getTargetTimespan();
    checkEquals(check, 1209600, "checkGetTargetTimespan.1");

    // TestNet2Params
    check = _params2.getTargetTimespan();
    checkEquals(check, 1209600, "checkGetTargetTimespan.2");
    
    // RegTestParams
    check = _params3.getTargetTimespan();
    checkEquals(check, 1209600, "checkGetTargetTimespan.3");


    // TestNet3Params
    check = _params4.getTargetTimespan();
    checkEquals(check, 1209600, "checkGetTargetTimespan.4");

    // UnitTestParams
    check = _params5.getTargetTimespan();
    checkEquals(check, 200000000, "checkGetTargetTimespan.5");
  }

  public void checkGetTransactionVerificationFlags(){ /* TODO */ }

  public void checkGetUriScheme(){
    String check;

    // MainNetParams
    check = _params1.getUriScheme();
    checkEquals(check, "bitcoin", "checkGetUriScheme.1");
    
    // TestNet2Params
    check = _params2.getUriScheme();
    checkEquals(check, "bitcoin", "checkGetUriScheme.2");
    
    // RegTestParams
    check = _params3.getUriScheme();
    checkEquals(check, "bitcoin", "checkGetUriScheme.3");

    // TestNet3Params
    check = _params4.getUriScheme();
    checkEquals(check, "bitcoin", "checkGetUriScheme.4");
 
    // UnitTestParams
    check = _params5.getUriScheme();
    checkEquals(check, "bitcoin", "checkGetUriScheme.5");
  }

  public void checkHashCode(){

    int hash1 = _params1.hashCode();
    int hash2 = _params2.hashCode();
    int hash3 = _params3.hashCode();
    int hash4 = _params4.hashCode();
    int hash5 = _params5.hashCode();

    // the overrides of 'equals' and 'hashCode' are inconsistent. Equality
    // takes class into account (as it should) while hash is only based on 
    // id. However, instances of TestNet2Params and TestNet3Params happen
    // to have the same ids, hence the same hash while being different.
    
    logMessage("-> NetworkParameters::hashCode see unit testing code ...");
    checkEquals(hash2, hash4, "checkHashCode.1");
    checkEquals(_params2.getId(), _params4.getId(), "checkHashCode.2");

  }

  public void checkHasMaxMoney(){

    boolean check1 = _params1.hasMaxMoney();
    boolean check2 = _params2.hasMaxMoney();
    boolean check3 = _params3.hasMaxMoney();
    boolean check4 = _params4.hasMaxMoney();
    boolean check5 = _params5.hasMaxMoney();

    checkEquals(check1, true, "checkHashMaxMoney.1");
    checkEquals(check2, true, "checkHashMaxMoney.2");
    checkEquals(check3, true, "checkHashMaxMoney.3");
    checkEquals(check4, true, "checkHashMaxMoney.4");
    checkEquals(check5, true, "checkHashMaxMoney.5");

  }
  public void checkIsCheckpoint(){
    // returns true of the given height has a recorded checkpoint
    for(int i = 0; i < 1000000; ++i){
      boolean check;

      // MainNetParams
      Sha256Hash hash = _checkpoints.get(i);
      check = _params1.isCheckpoint(i);
      checkEquals(check, hash != null, "checkIsCheckpoint.1");

      // TestNet2Params
      check = _params2.isCheckpoint(i);
      checkEquals(check, false, "checkIsCheckpoint.2");

      // RegTestParams
      check = _params3.isCheckpoint(i);
      checkEquals(check, false, "checkIsCheckpoint.3");
      
      // TestNet3Params
      check = _params4.isCheckpoint(i);
      checkEquals(check, false, "checkIsCheckpoint.4");

      // UnitTestParams
      check = _params5.isCheckpoint(i);
      checkEquals(check, false, "checkIsCheckpoint.5");
    }
    
  }

  public void checkPassesCheckpoint(){

    byte[] bytes = getRandomBytes(32);
    Sha256Hash hash = Sha256Hash.wrap(bytes);

    for(int i = 0; i < 10000000; ++i){
      boolean check;

      // MainNetParams
      if(_params1.isCheckpoint(i)){
        Sha256Hash test = _checkpoints.get(i);
        check = _params1.passesCheckpoint(i, test);
        checkEquals(check, true, "checkPassesCheckpoint.0");
      } else {
        check = _params1.passesCheckpoint(i, hash);
        checkEquals(check, true, "checkPassesCheckpoint.1");
      }

      // TestNet2Params
      check = _params2.passesCheckpoint(i, hash);
      checkEquals(check, true, "checkPassesCheckpoint.2");

      // RegTestParams
      check = _params3.passesCheckpoint(i, hash);
      checkEquals(check, true, "checkPassesCheckpoint.3");

      // TestNet3Params
      check = _params4.passesCheckpoint(i, hash);
      checkEquals(check, true, "checkPassesCheckpoint.4");

      // UnitTestParams
      check = _params5.passesCheckpoint(i, hash);
      checkEquals(check, true, "checkPassesCheckpoint.5");
    }
  }

}
