// running bitcoinj-core-0.14.3.jar 
import java.math.BigInteger;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.DumpedPrivateKey;

public class Test2 {

  public static void checkEquals(BigInteger n1, BigInteger n2, String msg){
    if(!n1.equals(n2)){
      System.err.println("failure in " + msg + ":");
      System.err.println("n1 = " + n1.toString(16));
      System.err.println("n2 = " + n2.toString(16));
      System.exit(1);
    }
  }

  public static void main(String[] args){

    String mainAsString = NetworkParameters.ID_MAINNET;
    String testAsString = NetworkParameters.ID_REGTEST;

    NetworkParameters mainNet  = NetworkParameters.fromID(mainAsString); 
    NetworkParameters testNet  = NetworkParameters.fromID(testAsString); 

    // compressed key
    ECKey k1 = new ECKey();

    // same key uncompressed
    ECKey k2 = k1.decompress();

    // common private secret
    BigInteger secret = k1.getPrivKey();  // same as k2.getPrivKey()

    // 4 possible types of WIF
    String wifMain1 = k1.getPrivateKeyAsWiF(mainNet); // main, compressed
    String wifMain2 = k2.getPrivateKeyAsWiF(mainNet); // main, uncompressed
    String wifTest1 = k1.getPrivateKeyAsWiF(testNet); // test, compressed
    String wifTest2 = k2.getPrivateKeyAsWiF(testNet); // test, uncompressed

    // creating corresponding DumpedPrivateKey
    DumpedPrivateKey dpkMain1 = DumpedPrivateKey.fromBase58(null, wifMain1);
    DumpedPrivateKey dpkMain2 = DumpedPrivateKey.fromBase58(null, wifMain2);
    DumpedPrivateKey dpkTest1 = DumpedPrivateKey.fromBase58(null, wifTest1);
    DumpedPrivateKey dpkTest2 = DumpedPrivateKey.fromBase58(null, wifTest2);

    // reconstructing ECKey from DumpedPrivateKey
    ECKey keyMain1 = dpkMain1.getKey();
    ECKey keyMain2 = dpkMain2.getKey();
    ECKey keyTest1 = dpkTest1.getKey();
    ECKey keyTest2 = dpkTest2.getKey();

    // Testing all is fine (should also check compression status)
    checkEquals(secret, keyMain1.getPrivKey(), "test1");
    checkEquals(secret, keyMain2.getPrivKey(), "test2");
    checkEquals(secret, keyTest1.getPrivKey(), "test3");
    checkEquals(secret, keyTest2.getPrivKey(), "test4");

    // so far so good...
    
    // now creating DumpedPrivateKey objects from getPrivateKeyEncoded
    dpkMain1 = k1.getPrivateKeyEncoded(mainNet);
    dpkMain2 = k2.getPrivateKeyEncoded(mainNet);
    dpkTest1 = k1.getPrivateKeyEncoded(testNet);
    dpkTest2 = k2.getPrivateKeyEncoded(testNet);

    // again reconstructing ECKey from DumpedPrivateKey
    keyMain1 = dpkMain1.getKey();
    keyMain2 = dpkMain2.getKey();
    keyTest1 = dpkTest1.getKey();
    keyTest2 = dpkTest2.getKey();

    // testing is successful for uncompressed keys ...
    checkEquals(secret, keyMain2.getPrivKey(), "test6");
    checkEquals(secret, keyTest2.getPrivKey(), "test7");

    // ... but fails for compressed keys
    checkEquals(secret, keyMain1.getPrivKey(), "test8");
    checkEquals(secret, keyTest1.getPrivKey(), "test9");

    // the output shows a trailing suffix byte 0x01
    /*
    failure in test8:
    n1 = 3e27a3956811801724857245ae78dd8ba1ce3df60da2bb00a782cee66ed640ee
    n2 = 3e27a3956811801724857245ae78dd8ba1ce3df60da2bb00a782cee66ed640ee01
    */






  }
}
