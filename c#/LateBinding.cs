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

    Assembly ass = Assembly.GetExecutingAssembly();

    Type typeA = ass.GetType("A");

    object instance = Activator.CreateInstance(typeA);

    MethodInfo info = typeA.GetMethod("foo");

    string [] param = new string[2];
    param[0] = "hello";
    param[1] = "world";

    // This is the crunch: instance.foo(param[0],param[1])
    object obj = info.Invoke(instance,param);

    if(obj == null){
      Console.WriteLine("obj is null");
    }


  }
}

class A {
  public void foo(string s1, string s2){
    Console.WriteLine("foo is running " + s1 + ":" + s2);}
}
      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
