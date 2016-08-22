import java.math.BigInteger;
import org.bitcoinj.core.VersionedChecksummedBytes;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.Base58;
import org.bitcoinj.params.MainNetParams;



public class Test4 {
  public static void main(String args[]){

    NetworkParameters mainNet = MainNetParams.get();
    String hex = "dba1e3e22415c56af772dee422add21b7382ea35f2af77852a8069d02e47ecf4";
    BigInteger big = new BigInteger(hex, 16); 
    ECKey key = ECKey.fromPrivate(big, false);  // uncompressed
    byte[] priv = key.getPrivKeyBytes();

    String wif1 = key.getPrivateKeyEncoded(mainNet).toBase58();
    System.out.println(wif1); // 5KV1o7tRK8pNqrPNYyi38nrik9r2Y85sjdgFDttnDiT1uZrQ1fj

    String wif2 = key.getPrivateKeyAsWiF(mainNet);
    System.out.println(wif2); // 5KV1o7tRK8pNqrPNYyi38nrik9r2Y85sjdgFDttnDiT1uZrQ1fj

    byte[] bytes = new byte[1 + 32 + 4];
    bytes[0] = (byte) 0x80;
    System.arraycopy(priv, 0, bytes, 1, 32);
    byte[] checksum = Sha256Hash.hashTwice(bytes, 0, 33);
    System.arraycopy(checksum, 0, bytes, 33, 4);
    String wif3 = Base58.encode(bytes);
    System.out.println(wif3); // 5KV1o7tRK8pNqrPNYyi38nrik9r2Y85sjdgFDttnDiT1uZrQ1fj
     
  }
}
