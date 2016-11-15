import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class AllTests extends TestSuite {

  // java -cp /usr/share/java/junit.jar:. junit.textui.TestRunner AllTests
  // java -cp /usr/share/java/junit.jar:. junit.singui.TestRunner AllTests

  static public Test suite() {

    TestSuite suite = new TestSuite();
    suite.addTestSuite(SimpleTest.class);
    return suite;

  }
}
