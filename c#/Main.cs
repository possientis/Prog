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

  static void Main(string[] args)
  {
    Console.WriteLine("Main thread starting ...");

    Thread worker1 = new Thread(BusyWait);
    Thread worker2 = new Thread(BusyWait);

    worker1.Start();
    worker2.Start();


    Console.WriteLine("Main thread ending ...");

  }

  public static void DoTimeConsumingWork(){
    Thread.Sleep(5000); // 5 sec

  }

  public static void BusyWait(){
    for(int i = 0; i < 1000000; ++i){
      Console.WriteLine("I am busy waiting");
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
 
