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

class Program
{

  static void Main(string[] args)
  {
    A a = new A();
    a.foo();

  }

}
// what is the point of partial method? separate declaration and definition
// so what? seems that the point is to have procedures with possibly missing// implementation. Probably makes it easy to write framework code.  
// so you can write code invoking procedures, whose implementation
// is optional
partial class A {
  partial void PartialMethod(); // only in partial class, only void
  public void foo(){
    PartialMethod();  // no implementation and yet....
  }
}

partial class A {
  partial void PartialMethod(){
    Console.WriteLine("PartialMethod is running");
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
 
