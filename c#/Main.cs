using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Xna.Framework;

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



    }
  }
}
