import java.security.SecureRandom;

public abstract class Test_Abstract implements Runnable {

  public abstract void run();

  private static final SecureRandom _random = new SecureRandom();

  protected static byte[] getRandomBytes(int n)
  {
    byte[] bytes = new byte[n];
    _random.nextBytes(bytes);
    return bytes;
  }

  protected static void logMessage(String message)
  {
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
      // in case equals override is not symmetric
      if(!right.equals(left))
      {
        logMessage(msg + ": checkEquals failure");
        logMessage("override of equals method is not symmetric");
        logMessage("left.equals(right) is true while right.equals(left) is false");
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

  protected static void checkNotNull(Object obj, String msg)
  {
    if(obj == null)
    {
      logMessage(msg + ": checkNotNull failure");
      System.exit(1);
    }
  }

  protected static void checkCondition(boolean cond, String msg)
  {
    if(!cond)
    {
      logMessage(msg + ": checkCondition failure");
      System.exit(1);
    }
  }

  protected static void checkException(Runnable callbk, String name, String msg)
  {
    try
    {
      callbk.run();
      logMessage(msg + ": checkException failure: no exception detected");
      System.exit(1);
    }
    catch(Exception e)
    {
      if(!e.getClass().getName().equals("java.lang." + name))
      {
        logMessage(msg + ": checkException failure: wrong exception type");
        logMessage("Expected: java.lang." + name);
        logMessage("Actual: " + e.getClass().getName());
        System.exit(1);
      }
    }
  }
}
