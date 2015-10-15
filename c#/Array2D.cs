using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {

      int[,] mult = new int[2,4];
      int[,] mult2 = {{0,1,2,3},{5,6,7,8}};

      foreach(int num in mult2)
      {
        Console.WriteLine(num);
      }

      for(int i = 0; i < mult.GetLength(0); ++i)
        for(int j = 0; j < mult.GetLength(1); ++j)
        {
          mult[i,j] = i+j;
          Console.WriteLine(mult[i,j]);
        }



    }
  }
}
