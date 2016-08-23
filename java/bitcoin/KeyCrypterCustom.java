import org.bitcoinj.crypto.EncryptedData;
import org.bitcoinj.crypto.KeyCrypter;
import org.bitcoinj.wallet.Protos.Wallet.EncryptionType;
import org.spongycastle.crypto.params.KeyParameter;

public class KeyCrypterCustom implements KeyCrypter {
  
  public KeyParameter deriveKey(CharSequence password){
    return null;  // TODO
  }

  public EncryptedData encrypt(byte[] plainBytes, KeyParameter aesKey){
    return null; // TODO
  }

  public byte[] decrypt(EncryptedData cipherBytes, KeyParameter aesKey){
    return null;  // TODO
  }

  public EncryptionType getUnderstoodEncryptionType(){
    // not much choice here it seems :(
    return EncryptionType.ENCRYPTED_SCRYPT_AES;
  }

  public static void main(String[] args){
  }
}
