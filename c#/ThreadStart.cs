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

    A a = new A();

    Thread worker1 = new Thread(MyTask);
    Thread worker2 = new Thread(new ThreadStart(MyTask));
    Thread worker3 = new Thread(delegate(){MyTask();});
    Thread worker4 = new Thread(() => MyTask());
    Thread worker5 = new Thread(a.Run);
    Thread worker6 = new Thread(new ThreadStart(a.Run));
    Thread worker7 = new Thread(delegate(){a.Run();});
    Thread worker8 = new Thread(() => a.Run());

    worker1.Start();
    worker2.Start();
    worker3.Start();
    worker4.Start();
    worker5.Start();
    worker6.Start();
    worker7.Start();
    worker8.Start();


    Console.WriteLine("Main thread ending ...");

  }

  public static void MyTask(){
    for(int i = 0; i < 10; ++i){
      Thread.Sleep(100);
      Console.Write("i = {0} : ", i);
    }

  }
}

class A{
  public void Run(){
    Program.MyTask();
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
 
