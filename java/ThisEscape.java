import java.util.*;
import java.awt.*;
// Implicitely allowing the 'this' reference to escape. Don't do this
// Do not allow 'this' to escape during construction
public class ThisEscape {
  public ThisEscape(EventSource source) {
    source.registerListener(  // This is like starting a thread from the constructor
        new EventListener(){  // which will share the reference to 'this'
          public void onEvent(Event e) {
            // doSomething()
          }
        });
  }
}

class EventSource {
  public void registerListener(EventListener listener){
  }
}


// Using a factory method to prevent the this reference to escape during construction
class SafeListener {
  private final EventListener listener;
  private SafeListener() {  // constructor is private
    listener = new EventListener() {
      public void onEvent(Event e) {
        //doSomething(e);
      }
    };
  }
  public static SafeListener newInstance(EventSource source) {
    SafeListener safe = new SafeListener();
    source.registerListener(safe.listener);
    return safe;
  }
}
