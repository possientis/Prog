import java.util.concurrent.*;

// Sharing variables without synchronization: don't do this
public class NoVisibility {
  private static boolean ready;
  private static int number;

  private static class ReaderThread extends Thread {
    public void run(){
      while(!ready){  // may loop for ever, coz variable ready may never become visible
        Thread.yield();
      }
      System.out.println(number); // Reader thread may fail to see last updated value
    }
  }

  public static void main(String[] args){
    new ReaderThread().start();
    number = 42;
    ready = true;
  }
}
