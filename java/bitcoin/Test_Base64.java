import java.util.Arrays;
import java.io.IOException;
import java.io.ByteArrayOutputStream;
import org.spongycastle.util.encoders.Encoder;
import org.spongycastle.util.encoders.Base64Encoder;
import org.spongycastle.util.encoders.Base64;


public class Test_Base64 extends Test_Abstract {

  public void run(){
    logMessage("Base64 unit test running ...");
    checkDecodeByteToByte();
    checkDecodeStringToByte();
    checkDecodeStringToStream();
    checkEncodeByteToByte();
    checkEncodeByteToByteOffset();
    checkEncodeByteToStream();
    checkEncodeByteToStreamOffset();
    checkToBase64String();
    checkToBase64StringOffset();
  }

  private static final Encoder _encoder = new Base64Encoder();

  public void checkDecodeByteToByte(){ /* TODO */ }
  public void checkDecodeStringToByte(){ /* TODO */ }
  public void checkDecodeStringToStream(){ /* TODO */ }
  public void checkEncodeByteToByte(){ /* TODO */ }

  public void checkEncodeByteToByteOffset(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] ran = getRandomBytes(1);
    int offset = ran[0] & 0xff;

    int length1 = data1.length - offset;
    int length2 = data2.length - offset;
    int length3 = data3.length - offset;

    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(500);

    try
    {
      _encoder.encode(data1, offset, length1, baos1); 
      _encoder.encode(data2, offset, length2, baos2); 
      _encoder.encode(data3, offset, length3, baos3); 
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncodeByteToByte.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    byte[] code1 = Base64.encode(data1, offset, length1); // actual call
    byte[] code2 = Base64.encode(data2, offset, length2); // actual call
    byte[] code3 = Base64.encode(data3, offset, length3); // actual call

    checkCondition(Arrays.equals(check1, code1), "checkEncodeByteToByte.2");
    checkCondition(Arrays.equals(check2, code2), "checkEncodeByteToByte.3");
    checkCondition(Arrays.equals(check3, code3), "checkEncodeByteToByte.4");
  }

  public void checkEncodeByteToStream()       { /* TODO */ }
  public void checkEncodeByteToStreamOffset() { /* TODO */ }
  public void checkToBase64String()           { /* TODO */ }
  public void checkToBase64StringOffset()     { /* TODO */ }

}
