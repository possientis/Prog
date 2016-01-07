// Simple thread-safe counter using the java monitor pattern
public final class Counter {
  private long value = 0;               // guarded by 'this'
  public synchronized long getValue() {
    return value;
  }
  public synchronized long increment() {
    if (value == Long.MAX_VALUE)
      throw new IllegalStateException("counter overflow");
    return ++value;
  }
}
