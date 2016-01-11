// Thread-safe mutable point class
public class SafePoint {
  private int x, y; // guarded by 'this'. No 'final' keyword, hence mutable
  private SafePoint(int[] a) { this(a[0], a[1]); }
  // copy constructor should not be implemented as 'this(p.x,p.y)'
  // as this would lead to potential race conditions
  public SafePoint(SafePoint p) { this(p.get()); }
  public SafePoint(int x, int y) {
    this.x = x;
    this.y = y;
  }
  public synchronized int[] get() {
    return new int[] { x, y };
  }
  public synchronized void set(int x, int y) {
    this.x = x;
    this.y = y;
  }
}
