import org.bitcoinj.core.ECKey;
import org.bitcoinj.crypto.KeyCrypter;
import org.bitcoinj.crypto.KeyCrypterScrypt;

import org.spongycastle.crypto.params.KeyParameter;

public class Test11 {
  public static void main(String[] args){
    ECKey k1 = new ECKey(); // some random (compressed) key

    // encrypting k1
    KeyCrypter crypter = new KeyCrypterScrypt();
    KeyParameter aesKey = crypter.deriveKey("some arbitrary passphrase");
    ECKey k2 = k1.encrypt(crypter, aesKey);

    // a few checks
    System.out.println(k2.isCompressed()); // true
    System.out.println(k2.isEncrypted());  // true
    System.out.println(k2.isPubKeyOnly()); // true  (private key not available)
    System.out.println(k2.isWatching());   // false (but it has a private key)

    // now decompressing encrypted key
    ECKey k3 = k2.decompress();
   
    // a few more checks
    System.out.println(k3.isCompressed()); // false
    System.out.println(k3.isEncrypted());  // false (hmmm, really?)
    System.out.println(k3.isPubKeyOnly()); // true  (private key not available)
    System.out.println(k3.isWatching());   // true  (because there is none)

    // Esentially same public key, but third has leading byte 0x04 (uncompressed)
    System.out.println(k1.getPublicKeyAsHex());  // 03585c156c1449155420 ...
    System.out.println(k2.getPublicKeyAsHex());  // 03585c156c1449155420 ...
    System.out.println(k3.getPublicKeyAsHex());  // 04585c156c1449155420 ...
  }
}

