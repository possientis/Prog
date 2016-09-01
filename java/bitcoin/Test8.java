import java.security.SecureRandom;
import org.bitcoinj.core.Address;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.params.MainNetParams;

public class Test8 {

  private static final SecureRandom random = new SecureRandom();

  public static void main(String[] args){

    // main bitcoin network
    NetworkParameters main = MainNetParams.get();

    // some address object with random hash
    byte[] hash = new byte[20]; // hash 160
    random.nextBytes(hash);
    Address address1 = new Address(main, hash);

    // cloning address1 but no deep copy
    Address address2 = null;
    try { address2 = address1.clone(); } catch (Exception e){}

    System.out.println(address1.toString());
    System.out.println(address2.toString());
    
    // exposing adress1 internals
    hash = address1.getHash160();
    for(int i = 0; i < 20; ++i){
      hash[i] = (byte) 0x00;
    }

    System.out.println(address1.toString());
    System.out.println(address2.toString());

    /* output:
     *
     * 1qgbowZp2WT8qENu7gwu7AT6R6EmAzcji
     * 1qgbowZp2WT8qENu7gwu7AT6R6EmAzcji
     * 1111111111111111111114oLvT2
     * 1111111111111111111114oLvT2
     */
  }
}
