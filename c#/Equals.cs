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
    A b = new A(2);

    Console.WriteLine(a.Equals(b));
    Console.WriteLine(a.Equals(a));
    Console.WriteLine(a.Equals(null));
    Console.WriteLine(a.Equals(2));
  }

}

class A {
  public A(int a){this.a = a;}
  public int a {get;set;}
  public override bool Equals(object obj){
    if(obj == null) return false;
    if(!(obj is A)) return false;
    return (this.a == ((A) obj).a);
  }
  // will generate warning unless also overriden
  public override int GetHashCode(){
    return a.GetHashCode() ^ 6351541; // ^ = xor I think
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
 
