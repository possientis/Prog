import java.util.Arrays;
import java.io.OutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import org.spongycastle.util.encoders.Base64Encoder;

public class Test_Base64Encoder extends Test_Abstract 
{

  public void run()
  {
    logMessage("Base64Encoder unit test running ...");
    checkBase64Encoder();
    checkDecodeFromByte();
    checkDecodeFromString();
    checkEncode();
  }

  private static final String getAlphabet()
  {
    return "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  }
  private static final byte[] _decodingTable = new byte[128];
  private static final byte[] _alphabet = getAlphabet().getBytes();
  private static final byte _padding = (byte) '=';
  private static final byte _err = (byte) 0xff;

  static 
  {
    for(int i = 0; i < 128; ++i){
      _decodingTable[i] = _err;
    }

    for(int i = 0; i < 64; ++i){
      _decodingTable[_alphabet[i] & 0xff] = (byte) i;
    }
  }

  private void _encode(
      byte[]        data, 
      int           off, 
      int           length, 
      OutputStream  out)
  {
    int modulus = length % 3;
    int dataLength = (length - modulus);
    int a1, a2, a3;
    int b1, b2, b3, b4;

    for(int i = off; i < off + dataLength; i += 3)
    {
      a1 = data[i] & 0xff;
      a2 = data[i + 1] & 0xff;
      a3 = data[i + 2] & 0xff;

      b1 = (a1 >>> 2)               & 0x3f; // b1 = 00a1[7]...a1[2]
      b2 = ((a1 << 4) | (a2 >>> 4)) & 0x3f; // b2 = 00a1[1]a1[0]a2[7]...a2[4] 
      b3 = ((a2 << 2) | (a3 >>> 6)) & 0x3f; // b3 = 00a2[3]...a2[0]a3[7]a3[6]
      b4 = a3                       & 0x3f; // b4 = 00a3[5]...a3[0]

      try
      {
        out.write(_alphabet[b1]);
        out.write(_alphabet[b2]);
        out.write(_alphabet[b3]);
        out.write(_alphabet[b4]);
      }
      catch(IOException e)
      {
        checkCondition(false, "_encode.1");
      }
    }

   // tail
    switch(modulus)
    {
    case 0: // nothing left to do 
      break;
    case 1:
      a1 = data[off + dataLength] & 0xff;
      b1 = (a1 >>> 2) & 0x3f;
      b2 = (a1 << 4)  & 0x3f;
      try
      {
        out.write(_alphabet[b1]);
        out.write(_alphabet[b2]);
        out.write(_padding);
        out.write(_padding);
      }
      catch(IOException e)
      {
        checkCondition(false, "_encode.2");
      }
      break;
    case 2:
      a1 = data[off + dataLength] & 0xff;
      a2 = data[off + dataLength + 1] & 0xff;

      b1 = (a1 >>> 2)               & 0x3f;
      b2 = ((a1 << 4) | (a2 >>> 4)) & 0x3f;
      b3 = (a2 << 2)                & 0x3f;

      try
      {
        out.write(_alphabet[b1]);
        out.write(_alphabet[b2]);
        out.write(_alphabet[b3]);
        out.write(_padding);
      }
      catch(IOException e)
      {
        checkCondition(false, "_encode.3");
      }
      break;
    }
  }

  private void _decodeLastBlock(
      byte[]        data,
      int           offset, /* length is understood to be 4 */
      OutputStream  out)
  {
    byte d1, d2, d3, d4;
    byte b1, b2, b3, b4;
    int a1, a2, a3;


    d1 = data[offset];
    d2 = data[offset + 1];
    d3 = data[offset + 2];
    d4 = data[offset + 3];

    if(d3 == _padding)        /* last bock is 'd1d2=='    */
    {
      b1 = _decodingTable[d1 & 0xff];
      b2 = _decodingTable[d2 & 0xff];

      if(b1 == _err || b2 == _err)
      {
        checkCondition(false, "_decodeLastBlock.1");
      }

      a1 = ((b1 << 2) | (b2 >> 4)) & 0xff; 

      try
      {
        out.write((byte) a1);
      }
      catch(IOException e)
      {
        checkCondition(false, "_decodeLastBlock.2");
      }

    }
    else if(d4 == _padding)   /* last block is 'd1d2d3='  */
    {
      b1 = _decodingTable[d1 & 0xff];
      b2 = _decodingTable[d2 & 0xff];
      b3 = _decodingTable[d3 & 0xff];

      if(b1 == _err || b2 == _err || b3 == _err)
      {
        checkCondition(false, "_decodeLastBlock.3");
      }

      a1 = ((b1 << 2) | (b2 >> 4)) & 0xff;
      a2 = ((b2 << 4) | (b3 >> 2)) & 0xff;

      try
      {
        out.write((byte) a1);
        out.write((byte) a2);
      }
      catch(IOException e)
      {
        checkCondition(false, "_decodeLastBlock.4");
      }
    }
    else                      /* last block has no padding */
    {
      b1 = _decodingTable[d1 & 0xff];
      b2 = _decodingTable[d2 & 0xff];
      b3 = _decodingTable[d3 & 0xff];
      b4 = _decodingTable[d4 & 0xff];

      if(b1 == _err || b2 == _err || b3 == _err || b4 == _err)
      {
        checkCondition(false, "_decodeLastBlock.5");
      }

      a1 = ((b1 << 2) | (b2 >> 4)) & 0xff;
      a2 = ((b2 << 4) | (b3 >> 2)) & 0xff;
      a3 = ((b3 << 6) | b4)        & 0xff;

      try
      {
        out.write((byte) a1);
        out.write((byte) a2);
        out.write((byte) a3);
      }
      catch(IOException e)
      {
        checkCondition(false, "_decodeLastBock.6");
      }
    }
  }

  private void _decode(
      byte[]        data,
      int           offset,
      int           length,
      OutputStream  out)
  {
    byte d1, d2, d3, d4;
    byte b1, b2, b3, b4;
    int a1, a2, a3;

    checkEquals(length % 4, 0, "_decode.1");

    for(int i = offset; i < offset + length - 4; i += 4)
    {
      d1 = data[i];
      d2 = data[i + 1];
      d3 = data[i + 2];
      d4 = data[i + 3];

      b1 = _decodingTable[d1];
      b2 = _decodingTable[d2];
      b3 = _decodingTable[d3];
      b4 = _decodingTable[d4];

      if(b1 == _err || b2 == _err || b3 == _err || b4 == _err)
      {
        checkCondition(false, "_decode.2");
      }

      a1 = ((b1 << 2) | (b2 >> 4))  & 0xff;
      a2 = ((b2 << 4) | (b3 >> 2))  & 0xff;
      a3 = ((b3 << 6) | b4)         & 0xff;

      try
      {
        out.write(a1);
        out.write(a2);
        out.write(a3);
      }
      catch(IOException e)
      {
        checkCondition(false, "_decode.3");
      }

    }

    _decodeLastBlock(data, offset + length - 4, out);

  }


 
  public void checkBase64Encoder(){
    Base64Encoder encoder = new Base64Encoder();
    checkNotNull(encoder, "checkBase64Encoder.1");
  }

  public void checkDecodeFromByte(){

    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301);
    byte[] data3 = getRandomBytes(302);

    byte[] ran = getRandomBytes(1);
    int offset = ran[0] & 0xff;

    int length1 = data1.length - offset;
    int length2 = data2.length - offset;
    int length3 = data3.length - offset;

    Base64Encoder encoder = new Base64Encoder();

    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(500); // enough space

    try 
    {
      encoder.encode(data1, offset, length1, baos1);
      encoder.encode(data2, offset, length2, baos2);
      encoder.encode(data3, offset, length3, baos3);
    }
    catch(IOException e)
    {
      checkCondition(false, "checkDecodeFromByte.1");
    }

    // This is the thing we want to decode
    byte[] code1 = baos1.toByteArray();
    byte[] code2 = baos2.toByteArray();
    byte[] code3 = baos3.toByteArray();

    // We first append it to some random data
    byte[] ignored = getRandomBytes(offset);
    byte[] test1 = new byte[offset + 500];
    byte[] test2 = new byte[offset + 500];
    byte[] test3 = new byte[offset + 500];

    System.arraycopy(ignored, 0, test1, 0, offset);
    System.arraycopy(ignored, 0, test2, 0, offset);
    System.arraycopy(ignored, 0, test3, 0, offset);

    System.arraycopy(code1, 0, test1, offset, code1.length);
    System.arraycopy(code2, 0, test2, offset, code2.length);
    System.arraycopy(code3, 0, test3, offset, code3.length);


    // six buffers for decoding
    ByteArrayOutputStream baos4 = new ByteArrayOutputStream(300); // enough space
    ByteArrayOutputStream baos5 = new ByteArrayOutputStream(301); // enough space
    ByteArrayOutputStream baos6 = new ByteArrayOutputStream(302); // enough space

    ByteArrayOutputStream baos7 = new ByteArrayOutputStream(300); // enough space
    ByteArrayOutputStream baos8 = new ByteArrayOutputStream(301); // enough space
    ByteArrayOutputStream baos9 = new ByteArrayOutputStream(302); // enough space

    try
    {
      // library code
      encoder.decode(test1, offset, code1.length, baos4);
      encoder.decode(test2, offset, code2.length, baos5);
      encoder.decode(test3, offset, code3.length, baos6);
    }
    catch(IOException e)
    {
      checkCondition(false, "checkDecodeFromByte.2");
    }

    //  our code
    _decode(test1, offset, code1.length, baos7);
    _decode(test2, offset, code2.length, baos8);
    _decode(test3, offset, code3.length, baos9);

    // This is the data we started with
    byte[] init1 = new byte[length1];
    byte[] init2 = new byte[length2];
    byte[] init3 = new byte[length3];

    System.arraycopy(data1, offset, init1, 0, length1);
    System.arraycopy(data2, offset, init2, 0, length2);
    System.arraycopy(data3, offset, init3, 0, length3);

    // data decoded by library
    byte[] check1 = baos4.toByteArray();
    byte[] check2 = baos5.toByteArray();
    byte[] check3 = baos6.toByteArray();

    checkCondition(Arrays.equals(check1, init1), "checkDecodeFromByte.3");
    checkCondition(Arrays.equals(check2, init2), "checkDecodeFromByte.4");
    checkCondition(Arrays.equals(check3, init3), "checkDecodeFromByte.5");

    // data decoded by ourselves
    check1 = baos7.toByteArray();
    check2 = baos8.toByteArray();
    check3 = baos9.toByteArray();

    checkCondition(Arrays.equals(check1, init1), "checkDecodeFromByte.6");
    checkCondition(Arrays.equals(check2, init2), "checkDecodeFromByte.7");
    checkCondition(Arrays.equals(check3, init3), "checkDecodeFromByte.8");
  }

  public void checkDecodeFromString(){ /* TODO */ }

  public void checkEncode(){
    byte[] data1 = getRandomBytes(300);
    byte[] data2 = getRandomBytes(301); 
    byte[] data3 = getRandomBytes(302);

    byte[] ran = getRandomBytes(1);
    int offset = ran[0] & 0xff;

    int length1 = data1.length - offset;
    int length2 = data2.length - offset;
    int length3 = data3.length - offset;


    Base64Encoder encoder = new Base64Encoder(); 
    ByteArrayOutputStream baos1 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos2 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos3 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos4 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos5 = new ByteArrayOutputStream(500); // enough space
    ByteArrayOutputStream baos6 = new ByteArrayOutputStream(500); // enough space

    try 
    {
      encoder.encode(data1, offset, length1, baos1);
      encoder.encode(data2, offset, length2, baos2);
      encoder.encode(data3, offset, length3, baos3);
    }
    catch(IOException e)
    {
      checkCondition(false, "checkEncode.1");
    }

    _encode(data1, offset, length1, baos4);
    _encode(data2, offset, length2, baos5);
    _encode(data3, offset, length3, baos6);

    byte[] bytes1 = baos1.toByteArray();
    byte[] bytes2 = baos2.toByteArray();
    byte[] bytes3 = baos3.toByteArray();

    byte[] check1 = baos4.toByteArray();
    byte[] check2 = baos5.toByteArray();
    byte[] check3 = baos6.toByteArray();
    
    checkCondition(Arrays.equals(check1, bytes1), "checkEncode.2");
    checkCondition(Arrays.equals(check2, bytes2), "checkEncode.3");
    checkCondition(Arrays.equals(check3, bytes3), "checkEncode.4");

    String[] test =   {"","f",   "fo",  "foo", "foob",    "fooba",   "foobar"};
    String[] result = {"","Zg==","Zm8=","Zm9v","Zm9vYg==","Zm9vYmE=","Zm9vYmFy"};  

    for(int i = 0; i < test.length; ++i){
      byte[] data = test[i].getBytes();
      baos1 = new ByteArrayOutputStream(128); // more than enough
      baos2 = new ByteArrayOutputStream(128);

      try
      {
        encoder.encode(data, 0, data.length, baos1);
      }
      catch(IOException e)
      {
        checkCondition(false, "checkEncode.5");
      }

      _encode(data, 0, data.length, baos2);

      checkEquals(result[i], baos1.toString(), "checkEncode.5");
      checkEquals(result[i], baos2.toString(), "checkEncode.6");
    }
  }

}
