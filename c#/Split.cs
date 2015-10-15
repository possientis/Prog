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

      string[] names = {"Tom", "Paul", "Sally"};
      string name = string.Join(",",names);
      Console.WriteLine(name);
      string[] names2 = name.Split(',');
      for(int i = 0; i < names2.Length; ++i)
      {
        Console.WriteLine(names2[i]);
      }



    }
  }
}
