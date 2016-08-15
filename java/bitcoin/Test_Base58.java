import java.util.Set;
import java.util.TreeSet;
import java.util.Arrays;
import java.math.BigInteger;
import java.security.SecureRandom;

import org.bitcoinj.core.Base58;
import org.bitcoinj.core.ECKey;

public class Test_Base58 implements Test_Interface {

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

  private byte[] _decode(String input){
    // not really important, could be single byte with value 0
    if(input.isEmpty()){
      return new byte[0];
    }
    return stringToBigInteger(input).toByteArray();
  }

  private String getRandomBase58String(int numDigits){

    byte[] single = new byte[1];

    checkCondition(numDigits > 0, "getRandomBase58String.1");
    StringBuilder builder = new StringBuilder(numDigits);  
    for(int i = 0; i < numDigits; ++i){
      random.nextBytes(single);  
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
  private final SecureRandom random = new SecureRandom();


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
    byte[] check2 = _decode("");  // validating the validator
    checkCondition(check1.length == 0, "checkDecode.1");
    checkCondition(check2.length == 0, "checkDecode.2");
    // single digit number
    for(int i = 0; i < 58; ++i){
      String test = String.valueOf(alphabet[i]);
      check1 = Base58.decode(test);
      check2 = _decode(test);
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
        check2 = _decode(test);
        BigInteger n1 = new BigInteger(1, check1);
        BigInteger n2 = new BigInteger(1, check2);
        checkEquals(n1, BigInteger.valueOf(i*58 + j), "checkDecode.7");
        checkEquals(n2, BigInteger.valueOf(i*58 + j), "checkDecode.8");
      }
    }

    // random number
    String test = getRandomBase58String(52);  // 52 digits, similar to WiF
    check1 = Base58.decode(test);
    check2 = _decode(test);
    BigInteger n1 = new BigInteger(1, check1);
    BigInteger n2 = new BigInteger(1, check2);
    checkEquals(n1, n2, "checkDecode.9");
    // our validation code may return 0x00 as leading byte
    checkCondition(check2.length <= check1.length + 1, "checkDecode.10");
    checkCondition(check1.length <= check2.length, "checkDecode.10");
    if(check2.length > check1.length){
      checkCondition(check2[0] == (byte) 0x00, "checkDecode.11");
    }
  }

  public void checkDecodeChecked(){
    // TODO
  }

  public void checkDecodeToBigInteger(){
    // TODO
  }

  public void checkEncode(){
    // TODO
  }

}

