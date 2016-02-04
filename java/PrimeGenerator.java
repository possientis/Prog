import java.util.*;
import java.math.*;
import java.util.concurrent.*;

//Threadsafe
public class PrimeGenerator implements Runnable {
  // Guarded by 'this'
  private final List<BigInteger> primes = new ArrayList<>();
  private volatile boolean cancelled;

  public void run() {
    BigInteger p = BigInteger.ONE;
    while (!cancelled ) {
      p = p.nextProbablePrime();
      synchronized (this) {
        primes.add(p);
      }
    }
  }

  public void cancel() { cancelled = true;

  }

  public synchronized List<BigInteger> get() {
    //copy
    return new ArrayList<BigInteger>(primes);
  }

  private static List<BigInteger> aSecondOfPrimes() throws InterruptedException {
    PrimeGenerator generator = new PrimeGenerator();
    new Thread(generator).start();
    try {
      TimeUnit.SECONDS.sleep(5);
    } finally {
      generator.cancel();
    }
    return generator.get();
  }

  public static void main(String[] args){
    List<BigInteger> list;

    try{
      list = aSecondOfPrimes();
    } 
    catch(Exception e){
      System.out.println("Exception caught");
      list = null;
    }

    for(BigInteger x : list){
      System.out.print(x); System.out.print("\t");
    }
  }
}
