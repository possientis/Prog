import org.bitcoinj.core.ECKey;
import org.bitcoinj.crypto.LazyECPoint;
import java.math.BigInteger;
//import org.spongycastle.math.ec.ECPoint;

public class Test {
  public static void main(String[] args){

    ECKey key;
    BigInteger priv1 = new BigInteger("13840170145645816737842251482747434280357113762558403558088249138233286766301");
    BigInteger priv2 = new BigInteger("1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD",16);
    System.out.println(priv1.equals(priv2));  // true
    key = ECKey.fromPrivate(priv1);

    System.out.println(key);
    
  
  }
}
