import java.util.*;

public class MySynchHash {
  public Map<String, Date> lastLogin =
    Collections.synchronizedMap(new HashMap<String, Date>());
}


