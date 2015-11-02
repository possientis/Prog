using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {
      int[] A = new int[3];
      foo();
      foo(A);
      foo(1,2,3,4,5,6); // that is the real point of 'params'

    }
    
    static void foo(params int[] i){
      Console.WriteLine("Foo is running");
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
 
