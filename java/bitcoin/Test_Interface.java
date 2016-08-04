public interface Test_Interface {

  public void run();

  public default void logMessage(String message){
    System.err.println(message);
  }

  public default void checkEquals(Object left, Object right, String msg){
    if(!left.equals(right)){
      logMessage(msg + ": checkEquals failure");
      logMessage("left = " + left);
      logMessage("right = " + right);
      System.exit(1);
    }
  }

  public default void checkNotNull(Object obj, String msg){
    if(obj == null){
      logMessage(msg + ": checkNotNull failure");
      System.exit(1);
    }
  }

  public default void checkCondition(boolean cond, String msg){
    if(!cond){
      logMessage(msg + ": checkCondition failure");
      System.exit(1);
    }
  }




}
