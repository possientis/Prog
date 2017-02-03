import org.bitcoinj.core.Base58;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.params.MainNetParams;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Address;

class Test17 {
  public static void main(String[] args)
  {
    
    NetworkParameters main = MainNetParams.get(); // main bitcoin network

    // alphabet is "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

    // This is where we decide what we want to say. The base 58 alphabet
    // does not allow us to use 'l', 'I', 'O' or '0' but that's fine. 
    // We are trying to obtain a number which is 25 byte long with a leading
    // byte of 0x00. So we probably need to start with a leading '1', and 
    // we need to add some padding to the right.

    String target="1HeLLoWorLdHowAreYouiAmok111111111";

    // Let us express this number as an array of bytes (big-endian)
    byte[] bytes25 = Base58.decode(target);

    // let us check our number has the correct size
    System.out.println("Size = " + bytes25.length);  // 25 , good

    // let us check the leading byte is indeed 0x00
    System.out.println("bytes25[0] = " + bytes25[0]); // yes it is !

    // retrieving the first 21 bytes
    byte[] bytes21 = new byte[21];
    System.arraycopy(bytes25, 0, bytes21, 0, 21);

    // Let us get the double Sha256 hash of these 21 bytes
    byte[] hash = Sha256Hash.hashTwice(bytes21); 
    
    // Let us create the bytes of the address
    byte[] addr = new byte[25];

    // copying first 21 bytes to address
    System.arraycopy(bytes21, 0, addr, 0, 21);

    // appending first 4 bytes of hash to address
    System.arraycopy(hash, 0, addr, 21, 4);

    // encoding this 25 bytes address in Base 58
    String strAddr = Base58.encode(addr);

    // Address = "1HeLLoWorLdHowAreYouiAmojzzzzu7udH" , almost perfect !
    System.out.println("Address = " + strAddr);

    // let us check address is a valid bitcoin address
    Address address = Address.fromBase58(main, strAddr);  // no errors, good

  }
}

