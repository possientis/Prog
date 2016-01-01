// Non-thread-safe Mutable Integer Holder
// Not thread safe because the value field is accessed from both get and set
// without  synchronization. Among other hazards, it is susceptible to stale values:
// if one thread calls set, other threads calling get may or may not see that update. 
// 64-bits load and store may not be atomic for nonvolatile data. Even if we do not 
// care about stale value, it is not safe to use shared mutable data in multithreaded 
// programs unless they are declared volatile or guarded by a lock.

// Locking is not just about mutual exclusion; it is also about memory visibility.
// To ensure that all threads see the most up-to-date values of shared variables,
// the reading and writing threads must synchronize on a common lock.

public class MutableInteger {
  private int value;

  public int get() { return value; }
  public void set(int value) { this.value = value; }
}

class SynchronizedInteger {
  private int value;
  public synchronized int get() { return value; }
  public synchronized void set(int value) { this.value = value; }
}



