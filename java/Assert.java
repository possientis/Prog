// use of the assert statement
// need to launch program with -enableassertions option, or -ea for short
// java -ea Assert


import java.util.*;

public class Assert {
  public static void main(String[] args){
    assert(true);
    assertTrue(true);
    assertFalse(true);
  }

  public static void assertTrue(boolean condition){
    assert(condition);
  }

  public static void assertFalse(boolean condition){
    assert(!condition);
  }

}
