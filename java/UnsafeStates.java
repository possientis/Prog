// Allowing Internal Mutable State to Escape. Don't do this
// Publishing states in this way is problematic because any caller
// can modify its contents. What was supposed to be private state
// has effectively been made public.

public class UnsafeStates {
  private String[] states = new String[] {"AK", "AL", "NY"};
  public String[] getStates() { return states; }
}

