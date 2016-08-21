import org.bitcoinj.core.ECKey;

public class Test {

  public static void main(String[] args){

    // random compressed key
    ECKey k1 = new ECKey(); 

    // same key, but creation time is different
    ECKey k2 = ECKey.fromPrivate(k1.getPrivKey());

    // The two keys are deemed different, due to creation time
    System.out.println(k1.equals(k2));  // false

    // yet hashCode ignores time of creation
    System.out.println(k1.hashCode() == k2.hashCode()); // true

  }
}
