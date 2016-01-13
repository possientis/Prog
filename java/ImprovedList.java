import java.util.*;

// keyword 'abstract' here solely to allow compilation without
// full imlementation of List<T> interface
public abstract class ImprovedList<T> implements List<T> {
  private final List<T> list;
  public ImprovedList(List<T> list) { this.list = list; }
  public synchronized boolean putIfAbsent(T x) {
    boolean contains = list.contains(x);
    if (contains)
      list.add(x);
    return !contains;
  }
  public synchronized void clear() { list.clear(); }
  // ... similarly delegate other List methods
}
