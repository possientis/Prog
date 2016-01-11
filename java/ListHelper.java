import java.util.*;

// Non-thread-safe attempt to implement 'putIfAbsent'. Don't do this!
public class ListHelper<E> {
  public List<E> list = Collections.synchronizedList(new ArrayList<E>());
  // 
  // ...
  // 
  // we are using the wrong lock !!!! The list is synchronized with a different lock
  // which certainly is not the 'this' of ListHelper. so our putIfAbsent is not atomic.
  public synchronized boolean putIfAbsent(E x) {
    boolean absent = !list.contains(x);
    if (absent)
      list.add(x);
    return absent;
  }
}

class ListHelper2<E> {
  public List<E> list = Collections.synchronizedList(new ArrayList<E>());
  // ...
    public boolean putIfAbsent(E x) {
      // can only do this (client-side locking) with classes that do commit to their
      // locking strategy
      synchronized (list) { // we are using the right lock, but need to check doc
        boolean absent = !list.contains(x);
        if (absent)
          list.add(x);
        return absent;
      }
    }
}
