// very strange things can happen when data is shared across threads
// without sufficient synchronization

// class at risk of failure if not properly published
public class Holder {
  private int n;
  public Holder(int n) { this.n = n; }
  // A thread can see a stale value the first time it reads a field
  // and then a more up-to-date value the next time, which is why
  // assertSanity can throw Assertion Error.
  public void assertSanity() {
    if (n != n)
      throw new AssertionError("This statement is false.");
  }
}
