import org.bitcoinj.core.Address;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Base58;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.params.MainNetParams;

class Test15 {
  public static void main(String[] args)
  {
    String  str = "1GCqcweZTwwe1w2RMWwwQMKSFgQzgFZQUb";

    NetworkParameters main = MainNetParams.get();

    // The string address is just a number expressed in base 58
    // Let us parse this string as see the bytes of the underlying number
    // 0:
    // -90:-57:12:74:-120:32:80:101:-63:-45:59:23:-63:86:19:127:-88:-57:54:-63:
    // -86:-114:24:124:
    byte[] full = Base58.decode(str);
    for(int i = 0; i < full.length; ++i){
      System.out.print(full[i]+ ":");
    }

    // Let us compute the hash 160 of the address
    //-90:-57:12:74:-120:32:80:101:-63:-45:59:23:-63:86:19:127:-88:-57:54:-63:
    // These are the same 20 bytes as before
    Address addr = Address.fromBase58(main, str);
    System.out.print("\n");
    byte[] hash = addr.getHash160();
    for(int i = 0; i < hash.length; ++i){
      System.out.print(hash[i]+ ":");
    }

    // Let us see the first 21 bytes of the address
    // 0:-90:-57:12:74:-120:32:80:101:-63:-45:59:23:-63:86:19:127:-88:-57:54:-63:
    byte[] decode = Base58.decodeChecked(str);
    System.out.print("\n");
    for(int i = 0; i < decode.length; ++i){
      System.out.print(decode[i]+ ":");
    }

    // Let us compute the double sha256 hash of the first 21 bytes of the address
    // and display the first 4 bytes: -86:-114:24:124:
    // These first 4 bytes are exactly the last 4 bytes of the address above 
    byte[] check = Sha256Hash.hashTwice(decode);
    System.out.print("\n");
    for(int i = 0; i < 4; ++i){
      System.out.print(check[i]+ ":");
    }
  }
}
