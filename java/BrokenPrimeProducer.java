// Unreliable Cancellation that can leave producers stuck in a
// blocking operation; don't do this!
import java.util.concurrent.*;
import java.math.*;

public class BrokenPrimeProducer extends Thread {
  private final BlockingQueue<BigInteger> queue;
  private volatile boolean cancelled = false;

  BrokenPrimeProducer(BlockingQueue<BigInteger> queue) {
    this.queue = queue;
  }

  public void run() {

    try {
      BigInteger p = BigInteger.ONE;
      while (!cancelled)
        queue.put(p = p.nextProbablePrime());
    } catch (InterruptedException consumed) { }
  }

  public void cancel() { cancelled = true;
  }

  // static stuff inside this class for convenience
  private static void consumePrimes() throws InterruptedException {
    BlockingQueue<BigInteger> primes = new LinkedBlockingQueue<>();
    BrokenPrimeProducer producer = new BrokenPrimeProducer(primes);
    producer.start();
    try {
      while (needMorePrimes())
        consume(primes.take());
    } finally {
    producer.cancel();
    }
  }

  private static boolean needMorePrimes(){
    return false;
  }
  private static void consume(BigInteger prime){
  }

}
