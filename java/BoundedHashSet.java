import java.util.*;
import java.util.concurrent.*;

// Using Semaphore to bound a collection
public class BoundedHashSet<T> {
  private final Set<T> set;
  private final Semaphore sem;

  public BoundedHashSet(int bound) {
    this.set = Collections.synchronizedSet(new HashSet<T>());
    sem = new Semaphore(bound);
  }
  public boolean add(T o) throws InterruptedException {
    sem.acquire();
    boolean wasAdded = false;
    try {
      wasAdded = set.add(o);
      return wasAdded;
    }
    finally {
      if (!wasAdded)
        sem.release();
    }
  }
  public boolean remove(Object o) {
    boolean wasRemoved = set.remove(o);
    if (wasRemoved)
      sem.release();
    return wasRemoved;
  }

  public static void main(String[] args) {
    BoundedHashSet<String> set = new BoundedHashSet<>(5);

    try{
      set.add("abc");
      set.add("def");
      set.add("ghi");
      set.add("jkl");
      set.add("mno");
    } catch(Exception e){
      System.out.println("Something was caught ...");
    }

    Thread t1 = new Thread(() -> {
      try{
      set.add("pqr");
      System.out.println("6th element was added");
      } catch(InterruptedException e){/* ignore */}
    });

    Thread t2 = new Thread(){
      public void run(){
        try{
          set.add("stu");
          System.out.println("7th element was added");
        } catch(InterruptedException e){/* ignore */}
      }
    };

    t1.start();
    t2.start();

    System.out.println("Removing an element");
    set.remove("ghi");

    System.out.println("Removing another element");
    set.remove("jkl");

    System.out.println("Program terminating ...");
  }
}
