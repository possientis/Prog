// javac -cp bitcoinj-core-0.14.1.jar:guava-19.0.jar:jcip.jar Bitcoinj.java
import org.bitcoinj.core.*;
import org.bitcoinj.params.TestNet3Params;

public class Bitcoinj {
  public static void main(String[] args){
    ECKey key = new ECKey();
    NetworkParameters params = TestNet3Params.get();
    Address address = key.toAddress(params);
    System.out.println(address);

  }
}



