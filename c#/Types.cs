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

      bool b = true;
      float f = 1.2f; // need 'f' here
      double d = 1.2; // 64 bits

      double pi = Math.PI; // 128 bits. Need 'm' here
      decimal pi2 = 3.14159m; // 128 bits. Need 'm' here
      sbyte sb = -128;
      byte by= 255;
      int i = 2356;
      uint ui = 2992929;
      long l = 39393;
      ulong ul = 4040;

      Console.WriteLine(int.MinValue);
      Console.WriteLine(int.MaxValue);
      Console.WriteLine(ulong.MaxValue);
      Console.WriteLine(sbyte.MaxValue);
    }
  }
}
