import org.bitcoinj.core.ECKey;
import java.math.BigInteger;
import org.spongycastle.math.ec.ECPoint;

public class Test1 {
  public static void main(String[] args){

    // some private key example of 'Mastering Bitcoin'
    String s = "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";
    BigInteger secret = new BigInteger(s,16);
    ECPoint point = ECKey.publicPointFromPrivate(secret);
    point = point.normalize();
    BigInteger x = point.getAffineXCoord().toBigInteger();
    BigInteger y = point.getAffineYCoord().toBigInteger();

    // 3ddfa27b1a7e6944d36c02c35ade5c1d4977829e4415c5e023e1063344bfd3be
    System.out.println(x.toString(16));

    // a24d02cf6cf43609b1c00c9accd3d26478d8a14205d086ab4332347e8a5b825e
    System.out.println(y.toString(16));
  }
}
