import org.bitcoinj.core.ECKey;
import org.bitcoinj.crypto.KeyCrypter;
import org.bitcoinj.crypto.KeyCrypterScrypt;
import org.spongycastle.crypto.params.KeyParameter;

public class Test6 {

  public static void main(String[] args){

    ECKey k1 = new ECKey(); // some random key

    // encrypting a key
    KeyCrypter crypter1 = new KeyCrypterScrypt();
    KeyParameter aesKey1 = crypter1.deriveKey("some arbitrary passphrase");
    ECKey k2 = k1.encrypt(crypter1, aesKey1);
    System.out.println(k2.isEncrypted()); // true

    // decrypting a key
    KeyCrypter crypter2 = k2.getKeyCrypter();
    KeyParameter aesKey2 = crypter2.deriveKey("some arbitrary passphrase");
    ECKey k3 = k2.decrypt(aesKey2);
    System.out.println(k1.equals(k3));  // true
  }
}
