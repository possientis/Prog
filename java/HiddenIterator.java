import java.util.*;
// Iteration hidden within string concatenation. Don't do this!
public class HiddenIterator {
  // Guarded by 'this'
  private final Set<Integer> set = new HashSet<Integer>();
  public synchronized void add(Integer i) { set.add(i); }
  public synchronized void remove(Integer i) { set.remove(i); }
  public void addTenThings() {
    Random r = new Random();
    for (int i = 0; i < 10; i++)
      add(r.nextInt());
    System.out.println("DEBUG: added ten elements to " + set);
  }
}
