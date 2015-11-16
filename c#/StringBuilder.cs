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
    // string are immutable, unlike StringBuilder
    StringBuilder str = new StringBuilder("C#"); // System.Text
    str.Append(" Video");
    str.Append(" Tutorial");
    str.Append(" for");
    str.Append(" beginners");

    Console.WriteLine(str);

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
 
