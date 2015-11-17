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
    a.Add("john");
    Console.WriteLine(a[0]);
    a[0] = "paul";
    Console.WriteLine(a[0]);


  }

}

class A {
  public A(){list_ = new List<string>();}
  public void Add(string s){list_.Add(s);}
  public string this[int index]{
    get{
      return list_[index];
    }

    set{
      list_[index] = value;
    }
  }
  //
  private List<string> list_;
}

      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
