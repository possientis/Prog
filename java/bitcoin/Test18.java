import java.io.UnsupportedEncodingException;
import java.math.BigInteger;

import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.ECKey.ECDSASignature;

class Test18 {
  public static void main(String[] args)
  {

    // Choose some message
    String message = "Hello World!";
    System.out.println("message = " + message);


    // Convert message to bytes
    byte[] msgBytes = null;
   
    try
    {
     msgBytes = message.getBytes("UTF-8");
    }
    catch(UnsupportedEncodingException e)
    {
      System.err.println("UTF-8 encoding is not supported on this platform");
      System.err.println("Exiting program now ...");
      System.exit(1);
    }

    System.out.println("Bytes of message as follows:");
    dump(msgBytes);

    // Compute hash of message 
    Sha256Hash hash = Sha256Hash.of(msgBytes);
    System.out.println("hash = " + hash);


    // Choose private key
    // This is the usual example from Mastering Bitcoin
    String k = "1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD";
    BigInteger nkey = new BigInteger(k, 16);
    ECKey key = ECKey.fromPrivate(nkey);
    System.out.println("key = " + key);


    // sign hash of message with key
    ECKey.ECDSASignature sig = key.sign(hash);
    System.out.println("Signature of message as follows:");
    System.out.println("r = " + sig.r.toString(16));
    System.out.println("s = " + sig.s.toString(16));

  }

  public static void dump(byte[] bytes)
  {
    for(int i = 0; i < bytes.length; ++i){

      if(i != 0 && i % 16 == 0)
      {
        System.out.print("\n");
      }

      System.out.print(Integer.toString(bytes[i], 16) + " ");

    }

    System.out.print("\n");
  }


}

