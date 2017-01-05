import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.Base58;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.DumpedPrivateKey;
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey.ECDSASignature;
import javax.xml.bind.DatatypeConverter;

public class Test14 {

  public static void main(String[] args){


    // message (hash) to be signed with private key
    String msg ="15953935a135031bfec37d36a9d662aea43e1deb0ea463d6932ac6e537cb3e81";

    // an example of WiF for private key (taken from 'Mastering Bitcoin)
    String wif ="KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ";      

    // creating a key object from WiF
    DumpedPrivateKey dpk = DumpedPrivateKey.fromBase58(null, wif);
    ECKey key = dpk.getKey();

    // checking our key object
    NetworkParameters main =  MainNetParams.get();
    String check = key.getPrivateKeyAsWiF(main);
    System.out.println(wif.equals(check));  // true

    // creating Sha object from string
    Sha256Hash hash = Sha256Hash.wrap(msg);

    // creating signature
    ECDSASignature sig = key.sign(hash);

    // encoding
    byte[] res = sig.encodeToDER();
    
    // converting to hex
    String hex = DatatypeConverter.printHexBinary(res); 

    System.out.println(hex);  // 304502210081B528....

  }
}
