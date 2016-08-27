import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.VersionedChecksummedBytes;
import org.bitcoinj.core.Base58;
import org.bitcoinj.core.Sha256Hash;

public class Test_VersionedChecksummedBytes extends Test_Abstract {

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

  private String _getWiF(byte[] priv, boolean compressed, boolean test){
    // returns the base58 WiF corresponding to a private address
    // There are 4 possible WiF depending on the values of 2 boolean
    // flags: one flag indicates whether the public key associated with
    // the private key is meant to be compressed. Another flag indicates
    // whether the private key refer to an address on a test network 
   
    // the private key should always be 32 bytes
    checkCondition(priv.length == 32, "_getWiF.1");

    // The returned WiF is always a base58 encoding of some array of bytes
    // WiF = Base58.encode(addressBytes);
    // All we need to do is set up 'addressBytes' properly
    byte[] addressBytes = null;

    // addressBytes is made up as follows:
    //
    // 1. A single 'version' byte 0x80 (mainNet) or 0xEF (testNet)
    // 2. The 32 bytes of the private key
    // 3. If key corresponds to compressed key, an additional byte 0x01
    // 4. An additional 4 bytes for checksum

    // 1 + 32 + 1 + 4 = 38, 1 + 32 + 4 = 37
    int totalLength = compressed ? 38 : 37;

    addressBytes = new byte[totalLength];

    // setting up version byte
    addressBytes[0] = test ? (byte) 0xEF : (byte) 0x80;

    // setting up private key
    System.arraycopy(priv, 0, addressBytes, 1, 32);

    // setting up additional 0x01 byte if private key of compressed key
    if(compressed){
      addressBytes[33] = (byte) 0x01;
    }

    // setting up index of next byte to be set up (needed later)
    // This is also the number of bytes which have been set up so far.
    int index = compressed ? 34 : 33;

    // computing checksum
    byte[] checksum = Sha256Hash.hashTwice(addressBytes, 0, index);

    // the first 4 bytes of this hash are added to addressBytes
    System.arraycopy(checksum, 0, addressBytes, index, 4);

    // simply returning bytes in base 58 representation.
    return Base58.encode(addressBytes);
  }
 

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
    ECKey k1 = new ECKey();
    byte[] priv = k1.getPrivKeyBytes();
    ECKey k2 = k1.decompress();

    // main network, compressed
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    String s1 = _getWiF(priv, true, false); 
    checkEquals(v1.toBase58(), s1, "checkToBase58.1");
    // test network, compressed
    VersionedChecksummedBytes v2 = k1.getPrivateKeyEncoded(regTestNet);
    String s2 = _getWiF(priv, true, true);
    checkEquals(v2.toBase58(), s2, "checkToBase58.2");
    // main network, uncompressed
    VersionedChecksummedBytes v3 = k2.getPrivateKeyEncoded(mainNet);
    String s3 = _getWiF(priv, false, false);
    checkEquals(v3.toBase58(), s3, "checkToBase58.3");
    // test network, uncompressed
    VersionedChecksummedBytes v4 = k2.getPrivateKeyEncoded(regTestNet);
    String s4 = _getWiF(priv, false, true);
    checkEquals(v4.toBase58(), s4, "checkToBase58.4");
  }

  public void checkToString(){
    ECKey k1 = new ECKey();
    VersionedChecksummedBytes v1 = k1.getPrivateKeyEncoded(mainNet);
    VersionedChecksummedBytes v2 = k1.getPrivateKeyEncoded(regTestNet);
    checkEquals(v1.toString(), v1.toBase58(), "checkToString.1");
    checkEquals(v2.toString(), v2.toBase58(), "checkToString.2");
  }

}
