using System;
using System.IO;  // StreamReader
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.Reflection;
using System.Windows; // ??

class Program
{

  static void Main(string[] args)
  {
    Console.WriteLine(A.AreEqual(10,10));
    Console.WriteLine(A.AreEqual("abc","abc"));
    Console.WriteLine(B<int>.AreEqual(10,10));
    Console.WriteLine(B<string>.AreEqual("abc","abc"));
  }

}

class A {
  public void foo(){
    Console.WriteLine("foo is running");
  }
  public static bool AreEqual<T>(T val1, T val2){
    return val1.Equals(val2);
  }
}
class B<T> {
  public static bool AreEqual(T val1, T val2){
    return val1.Equals(val2);
  }
}
      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
