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

    // very ugly, and loose type safety
    ParameterizedThreadStart pts = new ParameterizedThreadStart(MyTask);
    Thread worker1 = new Thread(pts);
    worker1.Start(10);


    Thread worker2 = new Thread(()=> MyTask(10));
    worker2.Start();

    Thread worker3 = new Thread(MyTask);
    worker3.Start(10);

    // best solution it seems
    // no need to have 'task' take 'object' arguments
    Thread worker4 = new Thread(() => OtherTask(10));
    worker4.Start();

    // via helper class
    A a = new A(10);
    Thread worker5 = new Thread(a.Run);
    worker5.Start();

    Console.WriteLine("Main thread ending ...");

  }

  public static void MyTask(object count){
    int target;

    if(int.TryParse(count.ToString(),out target)){
      for(int i = 0; i < target; ++i){
        Thread.Sleep(100);
        Console.Write("i = {0} : ", i);
      }
    }

  }

  public static void OtherTask(int count){
    for(int i = 0; i < count; ++i){
      Thread.Sleep(100);
      Console.Write("i = {0} : ", i);
    }
  }
}

class A{
  private int a;
  public A(int a){this.a = a;}
  public void Run(){Program.OtherTask(a);}
}


      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
