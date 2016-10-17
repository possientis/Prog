import java.security.SecureRandom;

public abstract class Bench_Abstract implements Runnable 
{

  public abstract void run();

  private static final SecureRandom _random = new SecureRandom();

  protected static byte[] getRandomBytes(int n)
  {

    byte[] bytes = new byte[n];

    _random.nextBytes(bytes);

    return bytes;
  }

  protected static void logMessage(String message)
  {
    System.err.println(message);
  }

  protected static void benchmark(Runnable callbk, String name, int iterations)
  {
    long start = System.currentTimeMillis();

    for(int i = 0; i < iterations; ++i)
    {
      callbk.run();
    }

    long end = System.currentTimeMillis();

    double time  = (end - start)/1000.0;

    System.err.format(
        "Benchmark: %s, %d iterations ran in %.3f seconds\n", 
        name, iterations, time
    );

  }

}
