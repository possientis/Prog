import java.util.Arrays;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.security.MessageDigest;
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
    checkWrapReverse();
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

  public void checkHashTwice(){ /* TODO */ }
  public void checkHashTwiceOffsetLength(){ /* TODO */ }
  public void checkHashTwiceOffsetLength2(){ /* TODO */ }

  public void checkNewDigest(){
    MessageDigest digest = Sha256Hash.newDigest();
    checkEquals(digest.getAlgorithm(), "SHA-256", "checkNewDigest.1");
    checkEquals(digest.getDigestLength(), 32, "checkNewDigest.2");
  }


  public void checkOf(){ /* TODO */ }
  public void checkOfFromFile(){ /* TODO */ }
  public void checkToBigInteger(){ /* TODO */ }
  public void checktoString(){ /* TODO */ }
  public void checkTwiceOf(){ /* TODO */ }
  public void checkWrap(){ /* TODO */ }
  public void checkWrapFromString(){ /* TODO */ }
  public void checkWrapReverse(){ /* TODO */ }

}





