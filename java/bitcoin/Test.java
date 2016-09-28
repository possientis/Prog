import org.bitcoinj.core.ECKey;
import java.security.SignatureException;

public class Test
{
  public static void main(String[] args)
  {
    String message = "some arbitrary message";

    ECKey k1 = new ECKey();      // random , compressed
    ECKey k2 = k1.decompress();

    // Signature (r,s) encoded as 65 bytes, with leading byte
    // allowing key recovery (including compression status)
    String sig1 = k1.signMessage(message);  
    String sig2 = k2.signMessage(message);  

    // compression status is encoded in signature => differing leading byte
    System.out.println(sig1);   // INgDhkt98Mme9m9AQ+nqtjyvjj ...
    System.out.println(sig2);   // HNgDhkt98Mme9m9AQ+nqtjyvjj ...

    // signatures are verified succesfully
    try
    {
      k1.verifyMessage(message, sig1);  // compressed case
    }
    catch(SignatureException e)
    {
      System.out.println("it should not happen");
    }

    try
    {
      k2.verifyMessage(message, sig2);  // uncompressed case
    }
    catch(SignatureException e)
    {
      System.out.println("it should not happen");
    }

    // in fact, compression status is ignored ...
    try
    {
      k1.verifyMessage(message, sig2);  // should it throw ?
    }
    catch(SignatureException e)
    {
      System.out.println("it does not happen");
    }

  }
}
