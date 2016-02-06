import java.util.concurrent.*;

public class Test {

  public static void main(String[] args) {

    Runnable r = ()-> {System.out.println("Running"); throw new Exception(); };

    Thread t = new Thread(r);
    t.start();

  }
}
