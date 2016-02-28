// simulated CAS Operation
// the semantics of compare and swap
// compare and swap is a low level synchronization construct
// this code is obviously not an implementation of compare
// and swap but simply serves to illustrate its semantics

public class SimulatedCAS {
  // guarded by 'this'
  private int value;
  public synchronized int get() { return value; }
  public synchronized int compareAndSwap(int expectedValue, int newValue){
    int oldValue = value;
    if (oldValue == expectedValue)
      value = newValue;
    return oldValue;
  }
  // compare and set returns whether compare and swap succeeded rather than
  // old state value (returned by compare and swap)
  public synchronized boolean compareAndSet(int expectedValue, int newValue) {
    return (expectedValue == compareAndSwap(expectedValue, newValue));
  }
}

// compare-and-swap CAS
// non-blocking counter using CAS (compare and swap)
class CasCounter {
  private SimulatedCAS value;
  public int getValue() {
    return value.get();
  }
  public int increment() {
    int v;
    do {
      v = value.get();
    }
    while (v != value.compareAndSwap(v, v + 1));
    return v + 1;
  }
}
