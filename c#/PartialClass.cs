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
    a.bar();

  }

}

partial class A {
  public void foo(){Console.WriteLine("foo running");}
}

partial class A {

  public void bar(){Console.WriteLine("bar running");}
}


      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
