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
using System.Runtime.InteropServices; // [Optional] attribute
using System.Collections.ObjectModel;
using System.Threading;

class Program
{

  public static bool FindA(A x){
    return x.a == 12;
  }

  public static void Main(string[] args)
  {
    List<A> list =new List<A>(){
      new A(12),
      new A(7),
      new A(13)
    };

    //Func<A,int> func = (A x) => x.a;
    //IEnumerable<int> ints = list.Select(func);
    IEnumerable<int> ints = list.Select(x => x.a);
    foreach(int x in ints){
      Console.WriteLine("a = {0}", x);
    }

    //A a = list.Find(x => x.a == 12);
    //A a = list.Find((A x) => {return x.a == 12;});
    A a = list.Find((A x) => x.a == 12);
    //A a = list.Find(FindA);
    //A a = list.Find(new Predicate<A>(FindA));
    //A a = list.Find(delegate(A x){return x.a == 12;});

    if(a != null){
      Console.WriteLine("Object found: {0}", a.a);
    } else{
      Console.WriteLine("Object not found ...");
    }

  }

}

class A {
  public int a;
  public A(int a){this.a = a;}
}

      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
