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
using System.Runtime.InteropServices; // [Optional] attribute
using System.Collections.ObjectModel;
using System.Threading;

class Program
{
  private static int sum = 0;
  private static object _lock = new object(); // used to protect sum

  public static void Main(string[] args)
  {
    Console.WriteLine("Main thread starting ...");

    Thread worker1 = new Thread(MyTask);
    Thread worker2 = new Thread(MyTask);
    Thread worker3 = new Thread(MyTask);
    Thread worker4 = new Thread(MyTask);
    Thread worker5 = new Thread(MyTask);
    Stopwatch stop = new Stopwatch();
    stop.Start();
    worker1.Start();
    worker2.Start();
    worker3.Start();
    worker4.Start();
    worker5.Start();
    worker1.Join();
    worker2.Join();
    worker3.Join();
    worker4.Join();
    worker5.Join();
    stop.Stop();
    Console.WriteLine("Time elapsed: {0}", stop.Elapsed);
    Console.WriteLine("Sum = {0}", sum);
    if(_lock == null){}; // to avoid compiler warning if _lock not used

    Console.WriteLine("Main thread ending ...");

  }

  public static void MyTask(){
    for(int i = 0; i < 1000000; ++i){
    // ++sum;  // no synchronization, very quick but no correctness
    //  Interlocked.Increment(ref sum); // atomic ++sum; 
      lock(_lock){++sum;} // not same performance as atomic inc
    }
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
 
