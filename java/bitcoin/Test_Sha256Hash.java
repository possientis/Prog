import java.util.Arrays;
import java.io.FileOutputStream;
import java.io.File;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.security.MessageDigest;
import javax.xml.bind.DatatypeConverter;


import org.bitcoinj.core.Sha256Hash;
import com.google.common.primitives.Ints;

public class Test_Sha256Hash implements Test_Interface {

  public void run(){
    logMessage("Sha256Hash unit test running ...");
    checkLength();
    checkZeroHash();
    checkCompareTo();
    checkShaEquals();
    checkGetBytes();
    checkGetReversedBytes();
    checkHash();
    checkHashOffsetLength();
    checkHashCode();
    checkHashTwice();
    checkHashTwiceOffsetLength();
    checkHashTwiceOffsetLength2();
    checkNewDigest();
    checkOf();
    checkOfFromFile();
    checkToBigInteger();
    checktoString();
    checkTwiceOf();
    checkWrap();
    checkWrapFromString();
    checkWrapReversed();
  }

  private final SecureRandom random = new SecureRandom();
  private final String emptyHashAsString = getEmptyHashAsString();
  private final String helloWorldHashAsString = getHelloWorldHashAsString();
  private final byte[] helloWorldAsBytes = getHelloWorldAsBytes(); 
  private byte[] getRandomBytes(){
    byte[] result = new byte[32];
    random.nextBytes(result);
    return result;
  }

  private byte[] getRandomContent(){
    byte[] content = new byte[8192];
    random.nextBytes(content);
    return content;
  }

  private Sha256Hash getRandomHash(){
    return Sha256Hash.wrap(getRandomBytes());
  }

  private byte[] reverse(byte[] input){
    checkEquals(input.length, 32, "reverse.1");
    byte[] result = new byte[32];
    int index = 32;
    for(int i = 0; i < 32; ++i){
      result[--index] = input[i];
    }

    return result;
  }

  private String getEmptyHashAsString(){
    // sha256sum of empty content
    return "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
  }

  private String getHelloWorldHashAsString(){
    // sha256sum of "Hello world!\n"
    return "0ba904eae8773b70c75333db4de2f3ac45a8ad4ddba1b242f0b3cfc199391dd8";
  }

  private byte[] getHelloWorldAsBytes(){
    byte[] bytes = { (byte) 0x48, (byte) 0x65, (byte) 0x6c, (byte) 0x6c,
                     (byte) 0x6f, (byte) 0x20, (byte) 0x77, (byte) 0x6f,  
                     (byte) 0x72, (byte) 0x6c, (byte) 0x64, (byte) 0x21, 
                     (byte) 0x0a};
    return bytes;
  }

  public void checkLength(){
    checkEquals(32, Sha256Hash.LENGTH, "checkLength.1");
  }


  public void checkZeroHash(){
    Sha256Hash hash = Sha256Hash.ZERO_HASH;
    byte[] bytes = hash.getBytes();
    checkEquals(bytes.length, 32, "checkZeroHash.1");
    for(int i = 0; i < 32; ++i){
      checkEquals(bytes[i], (byte) 0x00, "checkZeroHash.2");
    }
  }

  public void checkCompareTo(){
    // comparision equivalent to comparing BigInteger where 
    // Sha256Hash raw bytes are interpreted as little endian
    for(int test = 0; test < 256; ++test){
      byte[] bytes1 = getRandomBytes();
      byte[] bytes2 = getRandomBytes();

      BigInteger n1 = new BigInteger(1, reverse(bytes1));
      BigInteger n2 = new BigInteger(1, reverse(bytes2));

      Sha256Hash hash1 = Sha256Hash.wrap(bytes1);
      Sha256Hash hash2 = Sha256Hash.wrap(bytes2);

      int c1 = hash1.compareTo(hash2);
      int c2 = n1.compareTo(n2);
  
      checkEquals(c1, c2, "checkCompareTo.1");
      checkEquals(hash1.compareTo(hash1), 0, "checkCompareTo.2");
      checkEquals(hash2.compareTo(hash2), 0, "checkCompareTo.3");
    }
  }

  public void checkShaEquals(){
    for(int test = 0; test < 256; ++test){
      Sha256Hash hash1 = getRandomHash();
      Sha256Hash hash2 = getRandomHash();
      checkEquals(hash1, hash1, "checkShaEquals.1");
      checkEquals(hash2, hash2, "checkShaEquals.1");
      checkCondition(!hash1.equals(hash2), "checkShaEquals.3");
      checkCondition(!hash2.equals(hash1), "checkShaEquals.3");
    }
  }

  public void checkGetBytes(){
    byte[] bytes = getRandomBytes();
    Sha256Hash hash = Sha256Hash.wrap(bytes);
    byte[] check = hash.getBytes();
    checkCondition(Arrays.equals(bytes, check), "checkGetBytes.1");
  }


  public void checkGetReversedBytes(){
    byte[] bytes = getRandomBytes();
    Sha256Hash hash = Sha256Hash.wrap(bytes);
    byte[] check1 = hash.getReversedBytes();
    byte[] check2 = reverse(bytes);
    checkCondition(Arrays.equals(check1, check2), "checkGetReversedBytes.1");
  }

  public void checkHash(){
    // only checking that hash(byte[]) is correctly implemented 
    // in terms of the overloaded version hash(byte[], int, int)
    byte[] content = getRandomContent();
    byte[] hash1 = Sha256Hash.hash(content);
    byte[] hash2 = Sha256Hash.hash(content, 0, content.length);
    checkCondition(Arrays.equals(hash1, hash2), "checkHash.1");

    // additional checks for known hashes
   
    // empty content
    byte[] empty = new byte[0];
    byte[] check = Sha256Hash.hash(empty);

    BigInteger n1 = new BigInteger(1, check);
    BigInteger n2 = new BigInteger(emptyHashAsString, 16);
    checkEquals(n1, n2, "checkHash.2");

    // "Hello world!\n"
   check = Sha256Hash.hash(helloWorldAsBytes);
   n1 = new BigInteger(1, check);
   n2 = new BigInteger(helloWorldHashAsString, 16);
   checkEquals(n1, n2, "checkHash.3");
  }
  
  public void checkHashOffsetLength(){
    // Validation relies on class MessageDigest being validated
    byte[] content = getRandomContent();
    byte[] hash1 = Sha256Hash.hash(content, 13, 8000);  // 13 & 8000 arbitary
    MessageDigest digest = Sha256Hash.newDigest();
    digest.update(content, 13, 8000);
    byte[] hash2 = digest.digest();
    checkCondition(Arrays.equals(hash1, hash2), "checkHashOffsetLength.1");
  }

  public void checkHashCode(){
    for(int test = 0; test < 256; ++test){
      Sha256Hash hash1 = getRandomHash();
      Sha256Hash hash2 = getRandomHash();
      int code1 = hash1.hashCode();
      int code2 = hash2.hashCode();
      // arguably not much of a check
      checkCondition(code1 != code2, "checkHashCode.1");
      // replicating current implementation (last 4 bytes)
      byte[] bytes = hash1.getBytes();
      int check = Ints.fromBytes(bytes[28], bytes[29], bytes[30], bytes[31]);
      checkEquals(check, code1, "checkHashCode.2");
    }
  }

  public void checkHashTwice(){
    // only checking that hashTwice(byte[]) is correctly implemented 
    // in terms of the overloaded version hashTwice(byte[], int, int)
    byte[] content = getRandomContent();
    byte[] hash1 = Sha256Hash.hashTwice(content);
    byte[] hash2 = Sha256Hash.hashTwice(content, 0, content.length);
    checkCondition(Arrays.equals(hash1, hash2), "checkHashTwice.1");
  }


  public void checkHashTwiceOffsetLength(){
    byte[] content = getRandomContent();
    byte[] hash1 = Sha256Hash.hashTwice(content, 13, 8000); // 13, 8000 arbitrary
    byte[] hash2 = Sha256Hash.hash(content, 13, 8000);
    byte[] hash3 = Sha256Hash.hash(hash2);
    checkCondition(Arrays.equals(hash1, hash3), "checkHashTwiceOffsetLength.1");
  }

  public void checkHashTwiceOffsetLength2(){

    // The semantics of hashTwice(byte[], int, int, byte[], int, int) may not
    // be clear from the prototype of the method itself.
    // In fact, the method returns the double hash (indicated by 'twice') 
    // of the concatenation of two contents each indicated by (byte[], int, int)
    //
    // Indicidentally, the way to obtain the hash of concatenated inputs
    // is illustrated by the following example:
    byte[] b0 = { (byte) 0xa0, (byte) 0xff, (byte) 0x34, (byte) 0x78 };
    // b0 is the concatenation of b1 and b2
    byte[] b1 = { (byte) 0xa0, (byte) 0xff };
    byte[] b2 = { (byte) 0x34, (byte) 0x78 };

    // hash of the concatenated input
    byte[] hash1 = Sha256Hash.hash(b0);

    // doing it in stages
    MessageDigest digest = Sha256Hash.newDigest();
    digest.update(b1);  // add b1 
    digest.update(b2);  // add b2
    byte[] hash2 = digest.digest(); // now hash

    // checking both hash coincide
    checkCondition(Arrays.equals(hash1, hash2), "checkHashTwiceOffsetLength2.1");

    // validation of hashTwice
    byte[] content1 = getRandomContent();
    byte[] content2 = getRandomContent();
    // say we want the double hash of the concantenation of:
    // 256 bytes of content1 (starting at offset 511) 
    // 512 bytes of content2 (starting at offset 4095)
    hash1 = Sha256Hash.hashTwice(content1, 511, 256, content2, 4095, 512);
    digest.reset();
    digest.update(content1, 511, 256);
    digest.update(content2, 4095, 512); 
    hash2 = digest.digest();                // single hash
    byte[] hash3 = Sha256Hash.hash(hash2);  // double hash
    checkCondition(Arrays.equals(hash1, hash3), "checkHashTwiceOffsetLength2.2");

    // Alternatively, we can concatenate ourselves then double hash:
    byte[] content3 = new byte[256 + 512];
    System.arraycopy(content1, 511, content3, 0, 256);
    System.arraycopy(content2, 4095, content3, 256, 512);
    byte[] hash4 = Sha256Hash.hashTwice(content3);
    checkCondition(Arrays.equals(hash1, hash4), "checkHashTwiceOffsetLength2.3");
  }

  public void checkNewDigest(){
    MessageDigest digest = Sha256Hash.newDigest();
    checkEquals(digest.getAlgorithm(), "SHA-256", "checkNewDigest.1");
    checkEquals(digest.getDigestLength(), 32, "checkNewDigest.2");
  }


  public void checkOf(){
    byte[] content = getRandomContent();
    Sha256Hash sha = Sha256Hash.of(content);
    byte[] hash1 = sha.getBytes();
    byte[] hash2 = Sha256Hash.hash(content);
    checkCondition(Arrays.equals(hash1, hash2), "checkOf.1");
  }

  public void checkOfFromFile(){

    // creating some random filename
    byte[] bytes = getRandomBytes();
    String filename = "checkOfFromFile_" + (new BigInteger(1,bytes)).toString(16);
    File file = new File(filename);
    file.deleteOnExit();

    // creating some random content
    byte[] content = getRandomContent();

    // creating a file with random content
    try {
      FileOutputStream out = new FileOutputStream(filename);
      out.write(content);
      out.close();
    } 
    catch(Exception e){
      checkCondition(false, "checkFromFile.1");
    }
    
    // hash of random content
    Sha256Hash hash1 = Sha256Hash.of(content);

    // hash of file
    Sha256Hash hash2 = null;

    try {
      hash2 = Sha256Hash.of(file);
    }
    catch(Exception e){
      checkCondition(false, "checkFromFile.2");
    }

    // checking both hashes coincide
    checkEquals(hash1, hash2, "checkFromFile.3");
  }


  public void checkToBigInteger(){
    Sha256Hash hash = getRandomHash();
    BigInteger n1 = hash.toBigInteger();
    BigInteger n2 = new BigInteger(1, hash.getBytes());
    checkEquals(n1, n2, "checkToBigInteger.1");
  }

  public void checktoString(){
    Sha256Hash hash = getRandomHash();
    String s1 = hash.toString();
    String s2 = DatatypeConverter.printHexBinary(hash.getBytes()).toLowerCase();
    checkEquals(s1, s2, "checkToString.1");
  }

  public void checkTwiceOf(){
    byte[] content = getRandomContent();
    Sha256Hash hash1 = Sha256Hash.twiceOf(content);
    Sha256Hash hash2 = Sha256Hash.wrap(Sha256Hash.hashTwice(content));
    checkEquals(hash1, hash2, "checkTwiceOf.1");
  }

  public void checkWrap(){
    byte[] bytes = getRandomBytes();
    Sha256Hash hash = Sha256Hash.wrap(bytes);
    checkCondition(Arrays.equals(bytes, hash.getBytes()), "checkWrap.1");
  }
  public void checkWrapFromString(){
    byte[] bytes = getRandomBytes();
    String s = DatatypeConverter.printHexBinary(bytes).toLowerCase();
    Sha256Hash hash1 = Sha256Hash.wrap(s);  // s needs to be lower case
    Sha256Hash hash2 = Sha256Hash.wrap(bytes);
    checkEquals(hash1, hash2, "checkWrapFromString.1");
  }

  public void checkWrapReversed(){
    byte[] bytes = getRandomBytes();
    Sha256Hash hash1 = Sha256Hash.wrapReversed(bytes);
    Sha256Hash hash2 = Sha256Hash.wrap(reverse(bytes));
    checkEquals(hash1, hash2, "checkWrapReversed.1");
  }

}



