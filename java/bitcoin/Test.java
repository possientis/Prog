import java.math.BigInteger;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Address;
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.params.TestNet3Params;

public class Test {

  public static void main(String[] args){

    // An example of private key from the book 'Mastering Bitcoin'
    String k = "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";

    // Converting our string encoding as an actual number
    BigInteger priv = new BigInteger(k,16);

    // Creating a key object from our private key, with compressed public key
    ECKey k1 = ECKey.fromPrivate(priv, true);

    // Creating a key object from our private key, with uncompressed public key
    ECKey k2 = ECKey.fromPrivate(priv, false);


    // 03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a
    System.out.println(k1.getPublicKeyAsHex()); // compressed

    // 04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a...
    //...07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb
    System.out.println(k2.getPublicKeyAsHex()); // uncompressed

    NetworkParameters main = MainNetParams.get();   // main bitcoin network
    NetworkParameters test = TestNet3Params.get();  // test bitcoin network

    Address addr1 = k1.toAddress(main); // main network, compressed
    Address addr2 = k1.toAddress(test); // test network, compressed
    Address addr3 = k2.toAddress(main); // main network, uncompressed
    Address addr4 = k2.toAddress(test); // test network, uncompressed

    System.out.println(addr1.toString()); // 1J7mdg5rbQyUHENYdx39WVWK7fsLpEoXZy
    System.out.println(addr2.toString()); // mxdivjAqQSQj4LrAMX1XLQidyfU3pCWeS7
    System.out.println(addr3.toString()); // 1424C2F4bC9JidNjjTUZCbUxv6Sa1Mt62x
    System.out.println(addr4.toString()); // miY1V5L3QDaZVjrMT2Sw2WhHn63GzsNFQB

  }
}
