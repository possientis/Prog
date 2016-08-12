import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.VersionedChecksummedBytes;

public class Test_VersionedChecksummedBytes implements Test_Interface {

  public void run(){
    logMessage("VersionedChecksummedBytes unit test running ...");
    checkClone();
    checkCompareTo();
    checkVCBEquals();
    checkGetVersion();
    checkHashCode();
    checkToBase58();
    checkToString();
  }

  private  NetworkParameters getMainNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_MAINNET);
  }

  private  NetworkParameters getRegTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_REGTEST);
  }

  private  NetworkParameters getTestNetNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_TESTNET);
  }

  private  NetworkParameters getUnitTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_UNITTESTNET);
  }

  private final NetworkParameters mainNet = getMainNetwork();
  private final NetworkParameters regTestNet = getRegTestNetwork();
  private final NetworkParameters testNetNet = getTestNetNetwork();
  private final NetworkParameters unitTestNet = getUnitTestNetwork();
 

  public void checkClone(){
    ECKey k1 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k1.getPrivateKeyEncoded(regTestNet);
    VersionedChecksummedBytes v3 = k1.getPrivateKeyEncoded(testNetNet);
    VersionedChecksummedBytes v4 = k1.getPrivateKeyEncoded(unitTestNet);
    VersionedChecksummedBytes w1 = null;
    VersionedChecksummedBytes w2 = null;
    VersionedChecksummedBytes w3 = null;
    VersionedChecksummedBytes w4 = null;

    try {
      w1 = v1.clone();
      w2 = v2.clone();
      w3 = v3.clone();
      w4 = v4.clone();
    } catch(Exception e){ checkCondition(false, "checkClone.1"); }

    checkEquals(v1, w1, "checkClone.2");
    checkEquals(v2, w2, "checkClone.2");
    checkEquals(v3, w3, "checkClone.2");
    checkEquals(v4, w4, "checkClone.2");
  } 

  public void checkCompareTo(){
    ECKey k1 = new ECKey();
    ECKey k2 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k2.getPrivateKeyEncoded(mainNet);
    int comp = v1.compareTo(v2);
    checkCondition(!(comp == 0), "checkCompare.1");
    checkEquals(v2.compareTo(v1), -comp, "checkCompare.2");
    checkEquals(v2.compareTo(v2), 0, "checkCompare.3");
    checkEquals(v1.compareTo(v1), 0, "checkCompare.3");
  }

  public void checkVCBEquals(){
    ECKey k1 = new ECKey();
    ECKey k2 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k2.getPrivateKeyEncoded(mainNet);
    checkCondition(!v1.equals(v2), "checkVCBEquals.1");
    checkCondition(!v2.equals(v1), "checkVCBEquals.2");
    checkCondition(v1.equals(v1), "checkVCBEquals.3");
    checkCondition(v2.equals(v2), "checkVCBEquals.3");
  }
  
  public void checkGetVersion(){
    ECKey k1 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k1.getPrivateKeyEncoded(regTestNet);
    VersionedChecksummedBytes v3 = k1.getPrivateKeyEncoded(testNetNet);
    VersionedChecksummedBytes v4 = k1.getPrivateKeyEncoded(unitTestNet);
    checkEquals(v1.getVersion(), 128, "checkGetVersion.1");
    checkEquals(v2.getVersion(), 239, "checkGetVersion.2");
    checkEquals(v3.getVersion(), 239, "checkGetVersion.3");
    checkEquals(v4.getVersion(), 239, "checkGetVersion.4");
  }

  public void checkHashCode(){
    ECKey k1 = new ECKey();
    ECKey k2 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k2.getPrivateKeyEncoded(mainNet);
    checkCondition(v1.hashCode() != v2.hashCode(), "checkHashCode.1");
  } 

  // This is the main functionality
  public void checkToBase58(){
    // TODO
  }

  public void checkToString(){
    ECKey k1 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k1.getPrivateKeyEncoded(regTestNet);
    checkEquals(v1.toString(), v1.toBase58(), "checkToString.1");
    checkEquals(v2.toString(), v2.toBase58(), "checkToString.2");
  }

}
