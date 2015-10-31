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
      string s = "100.20";

      //int i = int.Parse(s);
      double i = double.Parse(s);
      int j;
      bool b = int.TryParse(s, out j);

      Console.WriteLine(j);
      Console.WriteLine(b);

    }

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
 
