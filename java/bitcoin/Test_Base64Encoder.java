import org.spongycastle.util.encoders.Base64Encoder;

public class Test_Base64Encoder extends Test_Abstract {

  public void run(){
    logMessage("Base64Encoder unit test running ...");
    checkBase64Encoder();
    checkDecodeFromByte();
    checkDecodeFromString();
    checkEncode();
  }

  private final String getAlphabet(){
    return "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  }

  private final byte[] _alphabet = getAlphabet().getBytes();
  private final byte _padding = (byte) '=';

  public void checkBase64Encoder(){
    Base64Encoder encoder = new Base64Encoder();
    checkNotNull(encoder, "checkBase64Encoder.1");

  }

  public void checkDecodeFromByte(){ /* TODO */ }
  public void checkDecodeFromString(){ /* TODO */ }
  public void checkEncode(){ /* TODO */ }
}
