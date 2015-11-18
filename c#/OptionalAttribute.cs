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

class Program
{

  static void Main(string[] args)
  {

    foo(10);
    foo(20,30);
   

  }

  static void foo(int a, [Optional] int b){
    Console.WriteLine("a = {0}, b = {1}", a, b);
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
 
