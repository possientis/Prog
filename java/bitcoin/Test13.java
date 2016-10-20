import org.bitcoinj.core.ECKey;
import org.bitcoinj.crypto.LazyECPoint;
import org.spongycastle.math.ec.ECPoint;

public class Test13 {
  public static void main(String[] args){

    ECKey key = new ECKey();                    // some random (compressed) key
    ECPoint point = key.getPubKeyPoint();       // associated ECPoint
    LazyECPoint lazy = new LazyECPoint(point);  // essentially the same, but formally 'Lazy'

    System.out.println(lazy.equals(point));     // true 
    System.out.println(point.equals(lazy));     // false, equality not symmetric

    Object same = point;
    System.out.println(lazy.equals(same));     // false, but lazy.equals(point) = true

  }
}
