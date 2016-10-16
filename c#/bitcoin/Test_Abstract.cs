using System;
using System.Security.Cryptography;
using Random = System.Security.Cryptography.RandomNumberGenerator;

public abstract class Test_Abstract
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


  protected static void CheckEquals(object left, object right, string msg)
  {
    if(left != null)
    {
      if(!left.Equals(right))
      {
        LogMessage(msg + ": CheckEquals failure");
        LogMessage("left = " + left);
        LogMessage("right = " + right);
        Environment.Exit(1);
      }
    }
    else
    {
      if(right != null)
      {
        LogMessage(msg + ": CheckEquals failure");
        LogMessage("left is null, but right is not");
        Environment.Exit(1);  // java System.exit(1)
      }
    }
  }

  protected static void CheckNotNull(object obj, string msg)
  {
    if(obj == null)
    {
      LogMessage(msg + ": CheckNoNull failure");
      Environment.Exit(1);
    }
  }

  protected static void CheckCondition(bool cond, string msg)
  {
    if(!cond)
    {
      LogMessage(msg + ": CheckCondition failure");
      Environment.Exit(1);
    }
  }

  protected static void CheckException(Runnable callbk, string name, string msg)
  {
    try
    {
      callbk();
      LogMessage(msg + ": CheckException failure: no exception detected");
      Environment.Exit(1);
    }
    catch(Exception e)
    {
      if(!e.GetType().Name.Equals(name))
      {
        LogMessage(msg + ": CheckException failure: wrong exception type");
        LogMessage("Expected: " + name);
        LogMessage("Actual: " + e.GetType().Name);
        Environment.Exit(1);
      }
    }
  }

  protected static void CheckArrayEquals(byte[] a, byte[] b, string msg)
  {
    if(a.Length != b.Length)
    {
      LogMessage(msg + ": CheckArrayEquals failure");
      LogMessage("left has length" + a.Length);
      LogMessage("right has length {0}" + b.Length);
      Environment.Exit(1);
    }

    for(int i = 0; i < a.Length; ++i)
    {
      if(a[i] != b[i])
      {
        LogMessage(msg + ":CheckArrayEquals failure at index i = " + i);
        LogMessage("left = " + a[i]);
        LogMessage("right = " + b[i]);
      }
    }
  }
}
