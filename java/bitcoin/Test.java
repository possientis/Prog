import java.math.BigInteger;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.DumpedPrivateKey;

public class Test {
  public static void main(String[] args){

    NetworkParameters nw = NetworkParameters.fromID(NetworkParameters.ID_MAINNET); 
    ECKey k1 = new ECKey();
    DumpedPrivateKey d1 = k1.getPrivateKeyEncoded(nw);

    // hoping to recover key k1
    ECKey k2 = d1.getKey();

    // retrieving both private keys to check they are equal
    BigInteger n1 = k1.getPrivKey();
    BigInteger n2 = k2.getPrivKey();

    // In fact the two private keys are not equal, there seems to be a 'version'
    // byte '0x01' trailing at the end of k2's private key


    // 7f3e51f2a039bf242a3be5741cbf4ac56f26533215286621e4cc5202c79a0a3
    System.out.println(n1.toString(16));

    // 7f3e51f2a039bf242a3be5741cbf4ac56f26533215286621e4cc5202c79a0a301
    System.out.println(n2.toString(16));

  }
}
