// happens-before ordering
// lazy initialization holder class idiom
// ThreadSafe
// lazy initialization technique which does not require synchronization
public class ResourceFactory {
  // only purpose of class is to initialize resource.
  // JVM defers initializing the class until it is actually used.
  // and because class initialized with static initializer,
  // no additional synchronization is needed.
  // This ensures lazy initialization while ensuring the
  // the resource is safely published, i.e. that you do not
  // have a situation in which one thread initializes object
  // while another thread retrieves a reference to object
  // without a happens before relation guarantee, which 
  // would mean that a thread could see a partially 
  // constructed resource. Static initialization happens before
  // any thread can see the object.
  private static class ResourceHolder {
    public static Resource resource = new Resource();
  }
  public static Resource getResource() {
    return ResourceHolder.resource ;
  }
}

// double checked locking anti pattern (DCL). Don't do this !
// NotThreadSafe
class DoubleCheckedLocking {
  private static Resource resource;
  public static Resource getInstance() {
    if (resource == null) { // not safe without happens before ordering
      // thread could see non-null reference before object fully constructed
      synchronized (DoubleCheckedLocking.class) {
        if (resource == null)
          resource = new Resource();
      }
    }
    return resource;
  }
}

class Resource {}
