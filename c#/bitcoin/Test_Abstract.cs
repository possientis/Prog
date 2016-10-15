using System;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public abstract class Test_Abstract
{
  public abstract void Run();

  private static readonly Random _random = new RNGCryptoServiceProvider();

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


  protected static void CheckEquals(object left, object right, string msg)
  {
    // TODO
  }

  protected static void CheckNotNull(object obj, string msg)
  {
    // TODO
  }

  protected static void CheckCondition(bool cond, string msg)
  {
    // TODO
  }

  protected static void CheckException(Delegate callbk, string name, string msg)
  {
    // TODO
  }

}
