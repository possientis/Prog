using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;  //StreamWriter, StreamReader

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {

      string[] custs = new String[]{"Tom", "Paul", "Greg"};

      // C# 'using' statement to properly handle 'unmanaged' ressources
      using(StreamWriter sw = new StreamWriter("custs.txt"))
      {
        foreach(string cust in custs)
        {
          sw.WriteLine(cust);
        }
      }

      string custName = "";
      using(StreamReader sr = new StreamReader("custs.txt"))
      {
        while((custName = sr.ReadLine()) != null)
        {
          Console.WriteLine(custName);
        }
      }
    }
  }
}
