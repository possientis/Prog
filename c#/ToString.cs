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
    A a = new A(2);
    A b = new A(5);
    Console.WriteLine(a.ToString());
    Console.WriteLine(b.ToString());
    Console.WriteLine(Convert.ToString(a)); // will use A::ToString()

  }

}

class A {
  public A(int a){this.a = a;}
  public int a {get;set;}
  public override string ToString(){
    return "A:" + (this.a).ToString();
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
 
