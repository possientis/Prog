import java.util.*;
import java.math.*;
import java.util.concurrent.*;

public interface Computable<A, V> {
  V compute(A arg) throws InterruptedException;
}

class ExpensiveFunction implements Computable<String, BigInteger> {
  public BigInteger compute(String arg) {
    // after deep thought...
    return new BigInteger(arg);
  }
}

class Memoizer1<A, V> implements Computable<A, V> {

  private final Map<A, V> cache = new HashMap<>();
  private final Computable<A, V> c;

  public Memoizer1(Computable<A, V> c) { this.c = c; }
  
  public synchronized V compute(A arg) throws InterruptedException {
    V result = cache.get(arg);
    if (result == null) {
      result = c.compute(arg);
      cache.put(arg, result);
    }
    return result;
  }
}

class Memoizer2<A, V> implements Computable<A, V> {

  private final Map<A, V> cache = new ConcurrentHashMap<>();
  private final Computable<A, V> c;

  public Memoizer2(Computable<A, V> c) { this.c = c; }

  public V compute(A arg) throws InterruptedException {
    V result = cache.get(arg);
    if (result == null) {
      result = c.compute(arg);
      cache.put(arg, result);
    }
    return result;
  }
}

class Memoizer3<A, V> implements Computable<A, V> {

  private final Map<A, Future<V>> cache = new ConcurrentHashMap<>();
  private final Computable<A, V> c;

  public Memoizer3(Computable<A, V> c) { this.c = c; }

  public V compute(final A arg) throws InterruptedException {
    Future<V> f = cache.get(arg);
    if (f == null) {

      // Old syntax replaced by lambda syntax below
      /*
      Callable<V> eval = new Callable<V>() {
        public V call() throws InterruptedException {
          return c.compute(arg);
        }
      };
      */

      // hopefully, this lambda syntax is equivalent to old syntax
      Callable<V> eval = () -> c.compute(arg);  // throws InterruptedException?

      FutureTask<V> ft = new FutureTask<V>(eval);
      f = ft;
      cache.put(arg, ft);
      ft.run(); // call to c.compute happens here
    }
    try {
      return f.get();
    } catch (ExecutionException e) {
      throw launderThrowable(e.getCause());
    }
  }

  public static RuntimeException launderThrowable(Throwable t) {
    if (t instanceof RuntimeException)
      return (RuntimeException) t;
    else if (t instanceof Error)
      throw (Error) t;
    else
      throw new IllegalStateException("Not unchecked", t);
  }
}



class Memoizer<A, V> implements Computable<A, V> {

  private final ConcurrentMap<A, Future<V>> cache = new ConcurrentHashMap<>();
  private final Computable<A, V> c;

  public Memoizer(Computable<A, V> c) { this.c = c; }

  public V compute(final A arg) throws InterruptedException {
    while (true) {
      Future<V> f = cache.get(arg);
      if (f == null) {
        /*
        Callable<V> eval = new Callable<V>() {
          public V call() throws InterruptedException {
            return c.compute(arg);
          }
        };
        */
        Callable<V> eval = () -> c.compute(arg);

        FutureTask<V> ft = new FutureTask<V>(eval);
        f = cache.putIfAbsent(arg, ft);
        if (f == null) { f = ft; ft.run(); }
      }
      try {
        return f.get();
      } catch (CancellationException e) {
        cache.remove(arg, f);
      } catch (ExecutionException e) {
        throw launderThrowable(e.getCause());
      }
    }
  }

  public static RuntimeException launderThrowable(Throwable t) {
    if (t instanceof RuntimeException)
      return (RuntimeException) t;
    else if (t instanceof Error)
      throw (Error) t;
    else
      throw new IllegalStateException("Not unchecked", t);
  }
}

