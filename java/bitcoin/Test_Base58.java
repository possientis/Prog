import java.util.Set;
import java.util.TreeSet;
import java.util.Arrays;
import java.math.BigInteger;

import org.bitcoinj.core.Base58;
import org.bitcoinj.core.ECKey;
import org.bitcoinj.core.Sha256Hash;

public class Test_Base58 extends Test_Abstract {

  public void run(){
    logMessage("Base58 unit test running ...");
    checkAlphabet();
    checkDecode();
    checkDecodeChecked();
    checkDecodeToBigInteger();
    checkEncode();
  }

  private String getAlphabetAsString(){
    // O and 0 could be confused
    // I and l could be confused
    // 0 is out         -> 9 characters
    // O and I are out  -> 24 characters
    // l is out         -> 25 characters
    // Total 9 + 24 + 25 = 58 characters
    // The order is important as it determines the value of each digit
    return "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
  }

  private int[] getDigitValues(){
    // returns an array of size 128 which encodes the value of a base 58 digit
    int[] array = new int[128];
    // so for example, the returned 'array' should satisfy:
    // array['1'] = 0
    // array['2'] = 1
    // ...
    // array['9'] = 8
    // array['A'] = 10
    // etc
    // being understood that array[i] = -1 if i = 0, .., 127 is not
    // the ascii code of a character belonging to the base58 alphabet.
    char[] alphabet = getAlphabetAsString().toCharArray(); 
    checkCondition(alphabet.length == 58, "getDigitValues.1");
    Arrays.fill(array, -1); 
    for(int i = 0; i < 58; ++i){
      int index = (int) alphabet[i];
      checkCondition(0 <= index, "getDigitValues.2");
      checkCondition(index < 128, "getDigitValues.3");
      array[index] = i;
    }
    return array;
  }


  private byte[] stringToBase58(String input){
    // converts a base58 string into a base58 number, namely a sequence
    // of bytes representing the value of each base58 digit.
    byte[] input58 = new byte[input.length()];
    for(int i = 0; i < input.length(); ++i){
      char c = input.charAt(i);
      int index = (int) c;
      int digit;
      if((0 <= index) && (index < 128)){
        digit = digitValues[index];
      } else {
        digit = -1;
      }
      checkCondition(digit != -1, "stringToBase58.1");
      input58[i] = (byte) digit;
    }

    return input58;
  }

  private BigInteger stringToBigInteger(String input){
    // converts a base58 string into a BigInteger
    
    byte[] input58 = stringToBase58(input); // big endian
    int N = input58.length;
    BigInteger fiftyEight = BigInteger.valueOf(58);

    BigInteger result = BigInteger.ZERO;  
    for(int i = 0; i < N; ++i){
      result = result.multiply(fiftyEight);
      result = result.add(BigInteger.valueOf(input58[i]));
    }

    return result;
  }

  private byte[] stringToBytes(String input){
    // not really important, could be single byte with value 0
    if(input.isEmpty()){
      return new byte[0];
    }
    byte[] bytes = stringToBigInteger(input).toByteArray();

    // the method toByteArray returns a 2-complement representation of 
    // a BigInteger. This means that it may add a leading 0x00 byte in 
    // order to indicate that the BigInteger being encoded is positive
    // So we test for this occurence and remove the leading null byte
    byte[] result = null;

    if(bytes[0] == (byte) 0x00 && bytes.length > 1){
      result = new byte[bytes.length - 1];
      System.arraycopy(bytes, 1, result, 0, bytes.length - 1);
    } else {
      result = bytes;
    }

    return result;
  }


  private byte[] bytesToBase58(byte[] input){

    if(input.length == 0) return new byte[0];
    BigInteger _58 = BigInteger.valueOf(58);

    BigInteger N = new BigInteger(1, input);
    byte[] temp = new byte[2 * input.length];       // upper bound on size
    int index = temp.length;
    do {
      BigInteger[] res = N.divideAndRemainder(_58); // N = 58*res[0] + res[1]
      temp[--index] = (byte) res[1].intValue();     // temp[--index] = N % 58
      N = res[0];                                   // N = N div 58
    } while (N != BigInteger.ZERO);

    int size = temp.length - index;
    byte [] result = new byte[size];
    System.arraycopy(temp, index, result, 0, size);

    return result;
  }

  private String base58ToString(byte[] input){
    StringBuilder builder = new StringBuilder(input.length);
    for(int i = 0; i < input.length; ++i){
      checkCondition(0 <= input[i], "base58ToString.1");
      checkCondition(input[i] < 58, "base58ToString.2");
      builder.append(alphabetAsString.charAt(input[i]));
    }
    return builder.toString();
  }

  private String bytesToString(byte[] input){
    return base58ToString(bytesToBase58(input));
  }

  private String getRandomBase58String(int numDigits){

    byte[] single;

    checkCondition(numDigits > 0, "getRandomBase58String.1");
    StringBuilder builder = new StringBuilder(numDigits);  
    for(int i = 0; i < numDigits; ++i){
      single = getRandomBytes(1);
      int x = (int) single[0] % 58;
      if(x < 0){ x = x + 58; }
      checkCondition(0 <= x, "getRandomBase58String.2");
      checkCondition(x < 58, "getRandomBase58String.3");
      builder.append(alphabetAsString.charAt(x));
    }

    return builder.toString();
  }


  private final String alphabetAsString = getAlphabetAsString();
  private final int[] digitValues = getDigitValues();


  public void checkAlphabet(){
    char [] alphabet1 = Base58.ALPHABET;
    checkCondition(alphabet1.length == 58, "checkAlphabet.1");
    Set<Character> set1 = new TreeSet<>();
    for(int i = 0; i < 58; ++i){
      set1.add(alphabet1[i]);
    }
    char [] alphabet2 = alphabetAsString.toCharArray();
    checkCondition(alphabet2.length == 58, "checkAlphabet.2");
    Set<Character> set2 = new TreeSet<>();
    for(int i = 0; i < 58; ++i){
      set2.add(alphabet2[i]);
    }
    checkEquals(set1, set2, "checkAlphabet.3");
    checkEquals(set1.hashCode(), set2.hashCode(), "checkAlphabet.4");
    // Actually checking Base58.ALPHABET as a set is prone to error, as
    // each base 58 digit has a value from 0 to 57 and such value cannot
    // be changed. if the code relies on ordering to determine the value
    // of a digit, then the order matters.

    for(int i = 0; i < 58; ++i){
      checkEquals(alphabet1[i], alphabet2[i], "checkAlphabet.5");
    }

  }

  public void checkDecode(){
    char[] alphabet = alphabetAsString.toCharArray();
    // empty string
    byte[] check1 = Base58.decode("");
    byte[] check2 = stringToBytes("");  // validating the validator
    checkCondition(check1.length == 0, "checkDecode.1");
    checkCondition(check2.length == 0, "checkDecode.2");
    // single digit number
    for(int i = 0; i < 58; ++i){
      String test = String.valueOf(alphabet[i]);
      check1 = Base58.decode(test);
      check2 = stringToBytes(test);
      checkCondition(check1.length == 1, "checkDecode.3");
      checkCondition(check2.length == 1, "checkDecode.4");
      checkEquals(check1[0], (byte) i, "checkDecode.5");
      checkEquals(check2[0], (byte) i, "checkDecode.6");
    }
    // two digits number
    for(int i = 0; i < 58; ++i){
      for(int j = 0; j < 58; ++j){
        String test = String.valueOf(alphabet[i]) + String.valueOf(alphabet[j]);
        check1 = Base58.decode(test);
        check2 = stringToBytes(test);
        BigInteger n1 = new BigInteger(1, check1);
        BigInteger n2 = new BigInteger(1, check2);
        checkEquals(n1, BigInteger.valueOf(i*58 + j), "checkDecode.7");
        checkEquals(n2, BigInteger.valueOf(i*58 + j), "checkDecode.8");
      }
    }

    // random number
    for(int i = 0; i < 1000; ++i){
      String test = getRandomBase58String(52);  // 52 digits, similar to WiF
      check1 = Base58.decode(test);
      check2 = stringToBytes(test);
      BigInteger n1 = new BigInteger(1, check1);
      BigInteger n2 = new BigInteger(1, check2);
      checkEquals(n1, n2, "checkDecode.9");
    }
  }

  public void checkDecodeChecked(){
    for(int i = 0; i < 1000; ++i){
      // random private key
      byte[] priv = getRandomBytes(32);
      // we do not need version byte or additional 0x01 byte for compressed key
      // here, as we are only testing that decodeChecked recovers the checked data
      byte[] checksum = Sha256Hash.hashTwice(priv,0,32);
      byte[] checked = new byte[36];
      // setting checked data
      System.arraycopy(priv, 0, checked, 0, 32);
      System.arraycopy(checksum, 0, checked, 32, 4);
      String checkedAsString = Base58.encode(checked);
      // hoping to recover initial data after calling function
      byte [] test = Base58.decodeChecked(checkedAsString);
      checkCondition(test.length == 32, "checkDecodeChecked.1");
      checkCondition(Arrays.equals(priv, test), "checkDecodeChecked.2");
    }
  }

  public void checkDecodeToBigInteger(){
    // random number
    for(int i = 0; i < 1000; ++i){
      String test = getRandomBase58String(52);
      BigInteger n1 = Base58.decodeToBigInteger(test);
      BigInteger n2 = stringToBigInteger(test);
      checkEquals(n1, n2, "checkDecodeToBigInteger.1");
    }
  }

  public void checkEncode(){
    for(int i = 0; i < 1000; ++i){
      String test = getRandomBase58String(52);
      byte[] bytes = Base58.decode(test);
      String s1 = Base58.encode(bytes);
      String s2 = bytesToString(bytes);
      // s1 s2 and test could differ by a leading '1' digit (which is zero)
      // So rather than testing equality on strings, we shall compare numbers
      BigInteger n = Base58.decodeToBigInteger(test);
      BigInteger n1 = Base58.decodeToBigInteger(s1);
      BigInteger n2 = Base58.decodeToBigInteger(s2);
      checkEquals(n, n1, "checkEncode.1");
      checkEquals(n, n2, "checkEncode.2");
    }
  }

}

