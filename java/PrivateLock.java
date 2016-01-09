// using a private lock rather than the intrisic (publicly accesible)
// object lock. Clients cannot acquire the lock. Verifying program
// correctness with publicly accessible lock is a lot harder.
public class PrivateLock {
  private final Object myLock = new Object();
  Widget widget;  // guarded by myLock
  void someMethod() {
    synchronized(myLock) {
      // Access or modify the state of widget
    }
  }
}


class Widget{
}
