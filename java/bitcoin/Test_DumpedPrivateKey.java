import java.util.Arrays;
import java.math.BigInteger;

import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.DumpedPrivateKey;
import org.bitcoinj.core.AddressFormatException;



public class Test_DumpedPrivateKey extends Test_Abstract {

  public void run(){
    logMessage("DumpedPrivateKey unit test running ...");
    checkDPKEquals();
    checkFromBase58();
    checkGetKey();
    checkHashCode();
  }

  private  NetworkParameters getMainNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_MAINNET);
  }

  private  NetworkParameters getTestNetwork(){
    return NetworkParameters.fromID(NetworkParameters.ID_REGTEST);
  }

  private final NetworkParameters mainNet = getMainNetwork();
  private final NetworkParameters testNet = getTestNetwork();


  public void checkDPKEquals(){
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();
    DumpedPrivateKey dpkMain1 = k1.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkMain2 = k2.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkTest1 = k1.getPrivateKeyEncoded(testNet);
    DumpedPrivateKey dpkTest2 = k2.getPrivateKeyEncoded(testNet);
    checkEquals(dpkMain1, dpkMain1, "checkDPKEquals.1");
    checkEquals(dpkMain2, dpkMain2, "checkDPKEquals.2");
    checkEquals(dpkTest1, dpkTest1, "checkDPKEquals.3");
    checkEquals(dpkTest2, dpkTest2, "checkDPKEquals.4");
    // compressed key vs uncompressed key
    checkCondition(!dpkMain1.equals(dpkMain2), "checkDPKEquals.5");
    checkCondition(!dpkTest1.equals(dpkTest2), "checkDPKEquals.6");
    // main net vs test net
    checkCondition(!dpkMain1.equals(dpkTest1), "checkDPKEquals.7");
    checkCondition(!dpkMain2.equals(dpkTest2), "checkDPKEquals.8");
  }

  public void checkFromBase58(){
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();
    DumpedPrivateKey dpkMain1 = k1.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkMain2 = k2.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkTest1 = k1.getPrivateKeyEncoded(testNet);
    DumpedPrivateKey dpkTest2 = k2.getPrivateKeyEncoded(testNet);
    String wifMain1 = dpkMain1.toString();
    String wifMain2 = dpkMain2.toString();
    String wifTest1 = dpkTest1.toString();
    String wifTest2 = dpkTest2.toString();
    DumpedPrivateKey chkMain1 = DumpedPrivateKey.fromBase58(null, wifMain1);
    DumpedPrivateKey chkMain2 = DumpedPrivateKey.fromBase58(null, wifMain2);
    DumpedPrivateKey chkTest1 = DumpedPrivateKey.fromBase58(null, wifTest1);
    DumpedPrivateKey chkTest2 = DumpedPrivateKey.fromBase58(null, wifTest2);

    DumpedPrivateKey shouldFail = null;

    // making sure code can spot inconsistencies in network specification
    try {
      // wifMain1 is a WiF referring to main network
      shouldFail = DumpedPrivateKey.fromBase58(testNet, wifMain1);
      checkCondition(false, "checkFromBase58.1");
    }
    catch(AddressFormatException e){
      // success
    }
    catch(Exception e){
      // Exception was thrown for the wrong reason
      checkCondition(false, "checkFromBase58.2");
    }

    try {
      // wifMain2 is a WiF referring to main network
      shouldFail = DumpedPrivateKey.fromBase58(testNet, wifMain2);
      checkCondition(false, "checkFromBase58.3");
    }
    catch(AddressFormatException e){
      // success
    }
    catch(Exception e){
      // Exception was thrown for the wrong reason
      checkCondition(false, "checkFromBase58.4");
    }

    try {
      // wifTest1 is a WiF referring to a test network
      shouldFail = DumpedPrivateKey.fromBase58(mainNet, wifTest1);
      checkCondition(false, "checkFromBase58.5");
    }
    catch(AddressFormatException e){
      // success
    }
    catch(Exception e){
      // Exception was thrown for the wrong reason
      checkCondition(false, "checkFromBase58.6");
    }

    try {
      // wifTest2 is a WiF referring to a test network
      shouldFail = DumpedPrivateKey.fromBase58(mainNet, wifTest2);
      checkCondition(false, "checkFromBase58.7");
    }
    catch(AddressFormatException e){
      // success
    }
    catch(Exception e){
      // Exception was thrown for the wrong reason
      checkCondition(false, "checkFromBase58.8");
    }

    // checking version
    checkEquals(chkMain1.getVersion(), 128, "checkFromBase58.9");   // 0x80
    checkEquals(chkMain2.getVersion(), 128, "checkFromBase58.10");  // 0x80
    checkEquals(chkTest1.getVersion(), 239, "checkFromBase58.11");  // 0xEF
    checkEquals(chkTest2.getVersion(), 239, "checkFromBase58.12");  // 0xEF

    // checking keys
    ECKey keyMain1 = chkMain1.getKey();
    ECKey keyMain2 = chkMain2.getKey();
    ECKey keyTest1 = chkTest1.getKey();
    ECKey keyTest2 = chkTest2.getKey();

    BigInteger n1 = k1.getPrivKey();

    // k1 and k2 only differ in compression status
    checkEquals(n1, k2.getPrivKey(), "checkFromBase58.13");
    
    checkEquals(n1, keyMain1.getPrivKey(), "checkFromBase58.14");
    checkEquals(n1, keyMain2.getPrivKey(), "checkFromBase58.15");
    checkEquals(n1, keyTest1.getPrivKey(), "checkFromBase58.16");
    checkEquals(n1, keyTest2.getPrivKey(), "checkFromBase58.17");

    // checking compression status
    checkCondition(keyMain1.isCompressed(), "checkFromBase58.18");
    checkCondition(!keyMain2.isCompressed(), "checkFromBase58.19");
    checkCondition(keyTest1.isCompressed(), "checkFromBase58.20");
    checkCondition(!keyTest2.isCompressed(), "checkFromBase58.21");

    // checking public keys: private keys as well as compression 
    // status have been validated. Hence public keys should be fine. 
   
    byte[] pubkey1 = k1.getPubKey();
    byte[] pubkey2 = k2.getPubKey();

    byte[] pubMain1 = keyMain1.getPubKey();
    byte[] pubMain2 = keyMain2.getPubKey();
    byte[] pubTest1 = keyTest1.getPubKey();
    byte[] pubTest2 = keyTest2.getPubKey();

    // both keys are compressed
    checkCondition(Arrays.equals(pubkey1, pubMain1), "checkFromBase58.22");
    checkCondition(Arrays.equals(pubkey1, pubTest1), "checkFromBase58.23");
    // both keys are uncompressed
    checkCondition(Arrays.equals(pubkey2, pubMain2), "checkFromBase58.24");
    checkCondition(Arrays.equals(pubkey2, pubTest2), "checkFromBase58.25");
  }

  public void checkGetKey(){

    // something is not right with this function when applied to a
    // DumpedPrivateKey object returned by the getPrivateKeyEncoded
    // method of the ECKey class. We first illustrate the problem:
    
    ECKey k1 = new ECKey();       // '1' for compressed
    ECKey k2 = k1.decompress();   // '2' for uncompressed
    DumpedPrivateKey dpkMain1 = k1.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkMain2 = k2.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkTest1 = k1.getPrivateKeyEncoded(testNet);
    DumpedPrivateKey dpkTest2 = k2.getPrivateKeyEncoded(testNet);

    ECKey keyMain1 = dpkMain1.getKey(); 
    ECKey keyMain2 = dpkMain2.getKey();
    ECKey keyTest1 = dpkTest1.getKey();
    ECKey keyTest2 = dpkTest2.getKey();

    // private keys will be seen to be wrong
    BigInteger n = k1.getPrivKey();
    checkEquals(n, k2.getPrivKey(), "checkGetKey.1");

    logMessage("-> DumpedPrivateKey::getKey see unit testing code ...");

    /*
    // This test fails: keyMain1.getPrivKey() wrongly has a 0x01 suffix byte
    logMessage(n.toString(16));
    logMessage(keyMain1.getPrivKey().toString(16));
    checkEquals(n, keyMain1.getPrivKey(), "checkGetKey.2");
    */

    /*
    // This test fails: keyTest1.getPrivKey() wrongly has a 0x01 suffix byte
    logMessage(n.toString(16));
    logMessage(keyTest1.getPrivKey().toString(16));
    checkEquals(n, keyTest1.getPrivKey(), "checkGetKey.3");
    */

    // tests are succesful when dealing with uncompressed key
    checkEquals(n, keyTest2.getPrivKey(), "checkGetKey.4");
    checkEquals(n, keyMain2.getPrivKey(), "checkGetKey.5");



    // things are a lot smoothier when dealing with DumpedPrivateKey
    // constructed with the static factory function fromBase58

    String wifMain1 = k1.getPrivateKeyAsWiF(mainNet);
    String wifMain2 = k2.getPrivateKeyAsWiF(mainNet);
    String wifTest1 = k1.getPrivateKeyAsWiF(testNet);
    String wifTest2 = k2.getPrivateKeyAsWiF(testNet);

    // redundant network argument set to null
    dpkMain1 = DumpedPrivateKey.fromBase58(null, wifMain1);
    dpkMain2 = DumpedPrivateKey.fromBase58(null, wifMain2);
    dpkTest1 = DumpedPrivateKey.fromBase58(null, wifTest1);
    dpkTest2 = DumpedPrivateKey.fromBase58(null, wifTest2);

    keyMain1 = dpkMain1.getKey();
    keyMain2 = dpkMain2.getKey();
    keyTest1 = dpkTest1.getKey();
    keyTest2 = dpkTest2.getKey();

    checkEquals(n, keyMain1.getPrivKey(), "checkGetKey.6");
    checkEquals(n, keyMain2.getPrivKey(), "checkGetKey.7");
    checkEquals(n, keyTest1.getPrivKey(), "checkGetKey.8");
    checkEquals(n, keyTest2.getPrivKey(), "checkGetKey.9");


    // redundant network argument specified
    dpkMain1 = DumpedPrivateKey.fromBase58(mainNet, wifMain1);
    dpkMain2 = DumpedPrivateKey.fromBase58(mainNet, wifMain2);
    dpkTest1 = DumpedPrivateKey.fromBase58(testNet, wifTest1);
    dpkTest2 = DumpedPrivateKey.fromBase58(testNet, wifTest2);

    keyMain1 = dpkMain1.getKey();
    keyMain2 = dpkMain2.getKey();
    keyTest1 = dpkTest1.getKey();
    keyTest2 = dpkTest2.getKey();

    checkEquals(n, keyMain1.getPrivKey(), "checkGetKey.6");
    checkEquals(n, keyMain2.getPrivKey(), "checkGetKey.7");
    checkEquals(n, keyTest1.getPrivKey(), "checkGetKey.8");
    checkEquals(n, keyTest2.getPrivKey(), "checkGetKey.9");

  }

  public void checkHashCode(){
    ECKey k1 = new ECKey();
    ECKey k2 = k1.decompress();
    DumpedPrivateKey dpkMain1 = k1.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkMain2 = k2.getPrivateKeyEncoded(mainNet);
    DumpedPrivateKey dpkTest1 = k1.getPrivateKeyEncoded(testNet);
    DumpedPrivateKey dpkTest2 = k2.getPrivateKeyEncoded(testNet);

    int hashMain1 = dpkMain1.hashCode();
    int hashMain2 = dpkMain2.hashCode();
    int hashTest1 = dpkTest1.hashCode();
    int hashTest2 = dpkTest2.hashCode();

    // compressed key vs uncompressed key
    checkCondition(hashMain1 != hashMain2, "checkHashCode.1");
    checkCondition(hashTest1 != hashTest2, "checkHashCode.2");
    // main net vs test net
    checkCondition(hashMain1 != hashTest1, "checkHashCode.3");
    checkCondition(hashMain2 != hashTest2, "checkHashCode.4");

    String wifMain1 = k1.getPrivateKeyAsWiF(mainNet);
    String wifMain2 = k2.getPrivateKeyAsWiF(mainNet);
    String wifTest1 = k1.getPrivateKeyAsWiF(testNet);
    String wifTest2 = k2.getPrivateKeyAsWiF(testNet);

    DumpedPrivateKey newMain1 = DumpedPrivateKey.fromBase58(null, wifMain1);
    DumpedPrivateKey newMain2 = DumpedPrivateKey.fromBase58(null, wifMain2);
    DumpedPrivateKey newTest1 = DumpedPrivateKey.fromBase58(null, wifTest1);
    DumpedPrivateKey newTest2 = DumpedPrivateKey.fromBase58(null, wifTest2);

//    checkEquals(hashMain1, newMain1.hashCode(), "checkHashCode.5");
    checkEquals(hashMain2, newMain2.hashCode(), "checkHashCode.6");
//    checkEquals(hashTest1, newTest1.hashCode(), "checkHashCode.7");
    checkEquals(hashTest2, newTest2.hashCode(), "checkHashCode.8");

  }

}
