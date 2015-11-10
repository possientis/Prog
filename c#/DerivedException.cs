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
      try{

        throw new MyException();

      }
      catch(MyException e){
        e.DisplayMessage();
      }
    }
  }

  class MyException : Exception{
    public void DisplayMessage(){
      Console.WriteLine("Exception");
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
 
