using System;
using System.IO;  // StreamReader
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
      StreamReader streamReader = new StreamReader("Main.cs");
      Console.WriteLine(streamReader.ReadToEnd());
      streamReader.Close();
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
 
