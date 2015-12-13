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

  delegate T OnDemand<T>();

  static Nullable<int> CreateSimpleNullable(int item){
    return new Nullable<int>(item);
  }

  static OnDemand<T> CreateSimpleOnDemand<T>(T item){
    return () => item;
  }

  static IEnumerable<T> CreateSimpleSequence<T>(T item){
    yield return item;
  }

  public static void Main(string[] args)
  {
    Nullable<int> x = new Nullable<int>();
    Console.WriteLine(x.HasValue);


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
 
