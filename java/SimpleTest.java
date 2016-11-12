import junit.framework.TestCase;

public class SimpleTest extends TestCase
{

  // java -cp /usr/share/java/junit.jar:. junit.textui.TestRunner SimpleTest
  // java -cp /usr/share/java/junit.jar:. junit.singui.TestRunner SimpleTest
  
  // sure you can call main if you want, but better run tests as above
  public static void main(String[] args) {
    SimpleTest test = new SimpleTest("simple");
    test.testSomething();
    test.testAnother();
  }

  // need to provide this constrctor
  public SimpleTest(String name) {
    super(name);
  }


  // called before each test
  public void setUp() {
    System.out.println("\nsetUp is running");
  }

  // called after each test
  public void tearDown() {
    System.out.println("tearDown is running");
  }

  // adding tests prefixed with 'test'
  public void testSomething() {
    System.out.println("testSomething is running");
    assertTrue(4 == (2 * 2));
  }

  public void testAnother() {
    System.out.println("testAnother is running");
    assertTrue(6 == (3 * 2));
  }
}
