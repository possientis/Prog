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
      const int SIZE = 1000000;


      Stopwatch stop = new Stopwatch();
      stop.Start();
      int[] array = new int[SIZE];
      for(int i = 0; i < SIZE; ++i){
        array[i] = i;
      }
      stop.Stop();
      Console.WriteLine(stop.Elapsed);


      stop.Restart();
      List<int> list = new List<int>(SIZE);
      for(int i = 0; i < SIZE; ++i){
        list.Add(i);
      }
      stop.Stop();
      Console.WriteLine(stop.Elapsed);


      stop.Restart();
      list.Insert(0,23);
      stop.Stop();
      Console.WriteLine(stop.Elapsed);

      stop.Restart();
      list.Add(54);
      stop.Stop();
      Console.WriteLine(stop.Elapsed);


    }



  }

}
