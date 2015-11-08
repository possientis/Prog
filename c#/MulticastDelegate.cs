using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace ConsoleApplication1
{
  // a delegate is a type safe function pointer
  public delegate void FooDelegate();

  class Program
  {
    public static void foo1(){
      Console.WriteLine("foo1 running");
    }
    public static void foo2(){
      Console.WriteLine("foo2 running");
    }
    public static void foo3(){
      Console.WriteLine("foo3 running");
    }


    static void Main(string[] args)
    {
      FooDelegate bar1,bar2,bar3,bar4,bar5;
      bar1 = new FooDelegate(foo1);
      bar2 = new FooDelegate(foo2);
      bar3 = new FooDelegate(foo3);

      bar4 = bar1 + bar2 + bar3;
      bar4();

      bar5 = bar4 - bar2;
      bar5();
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
 
