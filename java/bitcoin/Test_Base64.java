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
    checkEncodeByteToByteOff();
    checkEncodeByteToStream();
    checkEncodeByteToStreamOff();
    checkToBase64String();
    checkToBase64StringOff();
  }

  private static final Encoder _encoder = new Base64Encoder();

  public void checkDecodeByteToByte(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] code1 = Base64.encode(data1);
    byte[] code2 = Base64.encode(data2);
    byte[] code3 = Base64.encode(data3);


    byte[] check1 = Base64.decode(code1);
    byte[] check2 = Base64.decode(code2);
    byte[] check3 = Base64.decode(code3);


    checkCondition(Arrays.equals(check1, data1), "checkDecodeByteToByte.1");
    checkCondition(Arrays.equals(check2, data2), "checkDecodeByteToByte.2");
    checkCondition(Arrays.equals(check3, data3), "checkDecodeByteToByte.3");
  }


  public void checkDecodeStringToByte(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] code1 = Base64.encode(data1);
    byte[] code2 = Base64.encode(data2);
    byte[] code3 = Base64.encode(data3);

    String s1 = new String(code1);
    String s2 = new String(code2);
    String s3 = new String(code3);


    byte[] check1 = Base64.decode(s1);
    byte[] check2 = Base64.decode(s2);
    byte[] check3 = Base64.decode(s3);

    checkCondition(Arrays.equals(check1, data1), "checkDecodeStringToByte.1");
    checkCondition(Arrays.equals(check2, data2), "checkDecodeStringToByte.2");
    checkCondition(Arrays.equals(check3, data3), "checkDecodeStringToByte.3");
  }


  public void checkDecodeStringToStream(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] code1 = Base64.encode(data1);
    byte[] code2 = Base64.encode(data2);
    byte[] code3 = Base64.encode(data3);

    String s1 = new String(code1);
    String s2 = new String(code2);
    String s3 = new String(code3);

    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(300);
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(301);
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(302);

    try
    {
      Base64.decode(s1, baos1);
      Base64.decode(s2, baos2);
      Base64.decode(s3, baos3);
    }
    catch(IOException e)
    {
      checkCondition(false, "checkDecodeStringToStream.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    checkCondition(Arrays.equals(check1, data1), "checkDecodeStringToStream.1");
    checkCondition(Arrays.equals(check2, data2), "checkDecodeStringToStream.2");
    checkCondition(Arrays.equals(check3, data3), "checkDecodeStringToStream.3");

  }


  public void checkEncodeByteToByte(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(500);

    try
    {
      _encoder.encode(data1, 0, 300, baos1); 
      _encoder.encode(data2, 0, 301, baos2); 
      _encoder.encode(data3, 0, 302, baos3); 
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncodeByteToByte.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    byte[] code1 = Base64.encode(data1); // actual call
    byte[] code2 = Base64.encode(data2); // actual call
    byte[] code3 = Base64.encode(data3); // actual call

    checkCondition(Arrays.equals(check1, code1), "checkEncodeByteToByte.2");
    checkCondition(Arrays.equals(check2, code2), "checkEncodeByteToByte.3");
    checkCondition(Arrays.equals(check3, code3), "checkEncodeByteToByte.4");
  }

  public void checkEncodeByteToByteOff(){

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
      checkCondition(false, "checkEncodeByteToByteOff.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    byte[] code1 = Base64.encode(data1, offset, length1); // actual call
    byte[] code2 = Base64.encode(data2, offset, length2); // actual call
    byte[] code3 = Base64.encode(data3, offset, length3); // actual call

    checkCondition(Arrays.equals(check1, code1), "checkEncodeByteToByteOff.2");
    checkCondition(Arrays.equals(check2, code2), "checkEncodeByteToByteOff.3");
    checkCondition(Arrays.equals(check3, code3), "checkEncodeByteToByteOff.4");
  }

  public void checkEncodeByteToStream()       {

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(500);

    try
    {
      _encoder.encode(data1, 0, 300, baos1); 
      _encoder.encode(data2, 0, 301, baos2); 
      _encoder.encode(data3, 0, 302, baos3); 
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncodeByteToStream.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    ByteArrayOutputStream baos4 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos5 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos6 = new ByteArrayOutputStream(500);

    try
    {
      Base64.encode(data1, baos4); // actual call
      Base64.encode(data2, baos5); // actual call
      Base64.encode(data3, baos6); // actual call
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncodeByteToStream.2");
    }

    byte[] code1 = baos4.toByteArray();
    byte[] code2 = baos5.toByteArray();
    byte[] code3 = baos6.toByteArray();

    checkCondition(Arrays.equals(check1, code1), "checkEncodeByteToStream.3");
    checkCondition(Arrays.equals(check2, code2), "checkEncodeByteToStream.4");
    checkCondition(Arrays.equals(check3, code3), "checkEncodeByteToStream.5");
  }

  public void checkEncodeByteToStreamOff() {

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
      checkCondition(false, "checkEncodeByteToStreamOff.1");
    }

    byte[] check1 = baos1.toByteArray();
    byte[] check2 = baos2.toByteArray();
    byte[] check3 = baos3.toByteArray();

    ByteArrayOutputStream baos4 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos5 = new ByteArrayOutputStream(500);
    ByteArrayOutputStream baos6 = new ByteArrayOutputStream(500);

    try
    {
      Base64.encode(data1, offset, length1, baos4); // actual call
      Base64.encode(data2, offset, length2, baos5); // actual call
      Base64.encode(data3, offset, length3, baos6); // actual call
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncodeByteToStreamOff.2");
    }

    byte[] code1 = baos4.toByteArray();
    byte[] code2 = baos5.toByteArray();
    byte[] code3 = baos6.toByteArray();

    checkCondition(Arrays.equals(check1, code1), "checkEncodeByteToStreamOff.3");
    checkCondition(Arrays.equals(check2, code2), "checkEncodeByteToStreamOff.4");
    checkCondition(Arrays.equals(check3, code3), "checkEncodeByteToStreamOff.5");
 
  }

  public void checkToBase64String(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] code1 = Base64.encode(data1);
    byte[] code2 = Base64.encode(data2);
    byte[] code3 = Base64.encode(data3);

    String check1 = new String(code1);
    String check2 = new String(code2);
    String check3 = new String(code3);

    String s1 = Base64.toBase64String(data1);
    String s2 = Base64.toBase64String(data2);
    String s3 = Base64.toBase64String(data3);

    checkEquals(check1, s1, "checkToBase64String.1");
    checkEquals(check2, s2, "checkToBase64String.2");
    checkEquals(check3, s3, "checkToBase64String.3");
 
  }

  public void checkToBase64StringOff(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] ran = getRandomBytes(1);
    int offset = ran[0] & 0xff;

    int length1 = data1.length - offset;
    int length2 = data2.length - offset;
    int length3 = data3.length - offset;

    byte[] code1 = Base64.encode(data1, offset, length1);
    byte[] code2 = Base64.encode(data2, offset, length2);
    byte[] code3 = Base64.encode(data3, offset, length3);

    String check1 = new String(code1);
    String check2 = new String(code2);
    String check3 = new String(code3);

    String s1 = Base64.toBase64String(data1, offset, length1);
    String s2 = Base64.toBase64String(data2, offset, length2);
    String s3 = Base64.toBase64String(data3, offset, length3);

    checkEquals(check1, s1, "checkToBase64StringOff.1");
    checkEquals(check2, s2, "checkToBase64StringOff.2");
    checkEquals(check3, s3, "checkToBase64StringOff.3");
  } 

}
