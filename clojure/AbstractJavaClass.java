package gentest;

public abstract class AbstractJavaClass {

  public AbstractJavaClass(String a, String b) {
    System.out.println("Constructor: a, b");
  }

  public AbstractJavaClass(String a) {
    System.out.println("Constructor: a");
  }

  public abstract String getCurrentStatus();

  public String getSecret() {
    return "The Secret";
  }
}
