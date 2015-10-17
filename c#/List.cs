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

      List<int> numList = new List<int>();
      numList.Add(5);
      numList.Add(15);
      numList.Add(25);

      int[] randArray = {1,2,3,4,5};
      numList.AddRange(randArray);

      //List<int> numList2 = new List<int>(randArray);
      //List<int> numList3 = new List<int>(new int[] {1,2,3,4,5});
      numList.Insert(1,10);
      numList.RemoveAt(2);

      for(int i = 0; i < numList.Count; ++i)
      {
        Console.WriteLine(numList[i]);
      }

      Console.WriteLine("10 is in index " + numList.IndexOf(10));
      Console.WriteLine("25 in List: " + numList.Contains(25));

      List<string> strList = new List<string>(new string[]{"Tom","Paul"});
      Console.WriteLine("Tom in List: "
          + strList.Contains("tom",StringComparer.OrdinalIgnoreCase));

      strList.Sort();

    }
  }
}
