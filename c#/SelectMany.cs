using System;
using System.IO;  // StreamReader
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.Reflection;
using System.Windows; // ??
using System.Runtime.InteropServices; // [Optional] attribute
using System.Collections.ObjectModel;
using System.Threading;

class Program
{

  static IEnumerable<T> WhereHelper<T>(
      T item,
      Func<T,bool> predicate)
  {
    if(predicate(item))
      yield return item;
  }

  static IEnumerable<T> Where<T>(
      IEnumerable<T> items,
      Func<T,bool> predicate)
  {
    return items.SelectMany(item => WhereHelper(item, predicate));
  }

  public static void Main(string[] args)
  {

    Func<int, IEnumerable<int>> Odd = num => WhereHelper<int>(
      num,
      item => item % 2 != 0);

  
    IEnumerable<int> original = new List<int>(){3,6,7,8,1,2};
    IEnumerable<int> query = original.SelectMany(Odd);
    IEnumerable<int> query2 = original.Where(num => num % 2 != 0);

    foreach(int i in query){
      Console.WriteLine(i);
    }

    foreach(int i in query2){
      Console.WriteLine(i);
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
 
