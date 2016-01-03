import java.util.*;

// Immutable object built out of mutable underlying objects
public final class Immutable {
  private final Set<String> stooges = new HashSet<String>();
  public Immutable() {
    stooges.add("Moe");
    stooges.add("Larry");
    stooges.add("Curly");
  }
  public boolean isStooge(String name) {
    return stooges.contains(name);
  }

  public static void main(String[] args) {
    Immutable obj = new Immutable();
    System.out.println(obj.isStooge("Moe"));
    System.out.println(obj.isStooge("Patrick"));
  }
}
