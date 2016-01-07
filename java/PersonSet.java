import java.util.*;

// Using confinement to ensure thread safety
// No assumption is made about thread-safety of Person,
// but if it is mutable, additional synchronization will be needed
// when accessing a Person retrieved from a PersonSet
// 1. The most reliable way to do this is to make Person thread-safe
// 2. Less reliable is to guard the Person objects with a lock and ensure
// that all clients follow the protocol of acquiring the appropriate lock
// before accessing the Person
public class PersonSet {

  private final Set<Person> mySet = new HashSet<Person>(); // guarded by 'this'

  public synchronized void addPerson(Person p) {
    mySet.add(p);
  }

  public synchronized boolean containsPerson(Person p) {
    return mySet.contains(p);
  }

}

class Person {
}
