import java.security.Security;
import java.security.KeyFactory;
import java.security.KeyPairGenerator;
import java.security.SecureRandom;
import java.security.spec.ECGenParameterSpec;
import javax.crypto.Cipher;


public class Test {
  public static void main(String[] args){
    Security.insertProviderAt(new org.spongycastle.jce.provider.BouncyCastleProvider(), 1);
    KeyFactory f = KeyFactory.getInstance("EC", "SC"); // BC for java
    ECGenParameterSpec ecGenSpec = new ECGenParameterSpec("secp256k1");
    KeyPairGenerator g = KeyPairGenerator.getInstance("EC", "SC");
    g.initialize(ecGenSpec, new SecureRandom());
    Cipher ciper = Cipher.getInstance("ECIES/NONE/NOPADDING", "SC");
    ciper.init(Cipher.ENCRYPT_MODE, g.genKeyPair().getPrivate());
  }
}

