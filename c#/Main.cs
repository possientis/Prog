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

      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */

      A a = null;

      try{
      Console.WriteLine(a.a);
      } catch(NullReferenceException){
        Console.WriteLine("Exception was caught");
      }
      finally{
        Console.WriteLine("Cleaning up");
      }


    }



  }

  class A{
    public int a;
    public A(int a){this.a = a;}
  }

}
