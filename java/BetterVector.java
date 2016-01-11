import java.util.*;

// Check then Act ... requires synchronization
// Subclassing is a fragile solution. If underlying class
// were to change its synchronization policy by adopting a
// different lock than 'this', the class BetterVector
// would be broken
public class BetterVector<E> extends Vector<E> {
  public synchronized boolean putIfAbsent(E x) {
    boolean absent = !contains(x);
    if (absent)
      add(x);
    return absent;
  }
}
