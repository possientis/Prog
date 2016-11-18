import com.artima.greeter.Greeter;
import java.util.Date;

public class HiTime implements Greeter {
  public void greet() {
    // Date's no-arg constructor initializes itself to the
    // current date and time
    Date date = new Date();

    int hours = date.getHours();
    // Some hours: midnight, 0; noon, 12; 11PM, 23;
    if (hours >= 4 && hours <= 11) {
      System.out.println("Good morning, world!");
    }
    else if (hours >= 12 && hours <= 16) {
      System.out.println("Good afternoon, world!");
    }
    else if (hours >= 17 && hours <= 21) {
      System.out.println("Good evening, world!");
    }
    else if (hours >= 22 || hours <= 3) {
      System.out.println("Good night, world!");
    }
    else {
      // This should never happen.
      System.out.println("Oh oh, the clock is broken, world!");
    }
  }
}
