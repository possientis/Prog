using System;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;


public abstract class Bench_Abstract
{
  public abstract void Run();

  private static readonly Random _random = new RNGCryptoServiceProvider();

  protected delegate void Runnable();

  protected static byte[] GetRandomBytes(int n)
  {
    byte[] bytes = new byte[n];

    _random.GetBytes(bytes);

    return bytes;
  }

  protected static void LogMessage(string message)
  {
    Console.Error.WriteLine(message);
  }

  protected static void Benchmark(Runnable callbk, string name, int iterations)
  {
      // java System.currentTimeMillis() (returning long) for timing
      int start = Environment.TickCount;  // millis since system was started

      for(int i = 0; i < iterations; ++i)
      {
        callbk();
      }

      int end = Environment.TickCount;

      double time = (end - start)/1000.0;

      Console.Error.WriteLine(
          "Benchmark: {0}, {1} iterations ran in {2} seconds",
          name, iterations, time.ToString("0.000")
      );

  }

}


