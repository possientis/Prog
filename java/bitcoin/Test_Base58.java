import java.util.Set;
import java.util.TreeSet;
import org.bitcoinj.core.Base58;

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

  private final String alphabetAsString = getAlphabetAsString();


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
  }

  public void checkDecode(){
    // TODO
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

