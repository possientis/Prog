import java.security.SecureRandom;

public abstract class Test_Abstract implements Runnable {

  public abstract void run();

  private static final SecureRandom _random = new SecureRandom();

  protected static byte[] getRandomBytes(int n){
    byte[] bytes = new byte[n];
    _random.nextBytes(bytes);
    return bytes;
  }

  protected static void logMessage(String message){
    System.err.println(message);
  }

  protected static void checkEquals(Object left, Object right, String msg)
  {
    if(left != null)
    {
      if(!left.equals(right))
      {
        logMessage(msg + ": checkEquals failure");
        logMessage("left = " + left);
        logMessage("right = " + right);
        System.exit(1);
      }
    }
    else
    {
      if(right != null)
      {
        logMessage(msg + ": checkEquals failure");
        logMessage("left is null, but right is not");
        System.exit(1);
      }
    }
  }

  protected static void checkNotNull(Object obj, String msg){
    if(obj == null){
      logMessage(msg + ": checkNotNull failure");
      System.exit(1);
    }
  }

  protected static void checkCondition(boolean cond, String msg){
    if(!cond){
      logMessage(msg + ": checkCondition failure");
      System.exit(1);
    }
  }


}
