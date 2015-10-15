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

      int[] a = new int[5];
      int [] b = {3,5,6,7,2};


      for(int i = 0; i < 5; ++i)
      {
        a[i] = i;
        Console.WriteLine("({0},{1})",a[i],b[i]);
      }

    }
  }
}
