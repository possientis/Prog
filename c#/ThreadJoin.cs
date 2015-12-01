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

    Thread worker1 = new Thread(MyTask);
    Thread worker2 = new Thread(MyTask);
    worker1.Start();
    worker2.Start();

    if(worker1.IsAlive){
      Console.WriteLine("Thread 1 is alive ...");
    }
    worker1.Join(); // or worker1.Join(timeout)
    Console.WriteLine("\nThread1 complete ...");

    if(worker2.Join(1000)){
      Console.WriteLine("\nThread2 complete within 1 sec after thread1...");
    }

    Console.WriteLine("\nMain thread ending ...");

  }

  public static void MyTask(){

    for(int i = 0; i < 10; ++i){
      Thread.Sleep(100);
      Console.Write("i = {0} : ", i);
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
 
