import org.bitcoinj.core.*;
import org.bitcoinj.params.*;


public class Demo {
  public static void main(String[] args){

    // we'll use the tesnet network for now
    System.out.println("Retrieving testnet network ...");
    NetworkParameters params = TestNet3Params.get(); 

    // most basic operation: make a key and print its address for the screen
    System.out.println("Creating new key ...");
    ECKey key = new ECKey();

    // Conversion of key ot address depends on network type 
    System.out.println("Retrieving corresponding address ...");
    Address address = key.toAddress(params);
    System.out.println("Address = " + address);

    // keys record their creation time
    System.out.println("Key creation time = " + key.getCreationTimeSeconds());
    System.out.println("Setting creation time to zero ...");
    key.setCreationTimeSeconds(0);
    System.out.println("Key creation time = " + key.getCreationTimeSeconds());




  }
}
