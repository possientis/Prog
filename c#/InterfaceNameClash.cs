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
      A x = new A();
      ((I1)x).foo();  // need to disambiguate
      ((I2)x).foo();

      B y = new B();
      y.foo();
      ((I2)y).foo();
    }

  }
  
  interface I1{
    void foo();
  }
  interface I2{
    void foo();
  }

  class A : I1, I2{
    // no public keyword for explicit interface impl
    void I1.foo(){Console.WriteLine("I1");}
    void I2.foo(){Console.WriteLine("I2");}
  }
   class B : I1, I2{
    // no public keyword for explicit interface impl
    public void foo(){Console.WriteLine("I1");} //default Impl
    void I2.foo(){Console.WriteLine("I2");}
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
 
