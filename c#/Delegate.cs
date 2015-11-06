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
  public delegate void FooDelegate(string message);

  class Program
  {
    public static void foo(string message){
      Console.WriteLine(message);
    }

    public static void run(FooDelegate foo, string message){
      foo(message);
    }

    static void Main(string[] args)
    {
      FooDelegate fooDelegate = new FooDelegate(foo);
      fooDelegate("Hello from delegate");
      FooDelegate otherDelegate = new FooDelegate(message =>  Console.WriteLine("Lambda: "+ message));
      otherDelegate("this running delegate was instantiated from a C# lambda expression");
      run(x => Console.WriteLine(x),"Hello World"); // this is neat

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
 
