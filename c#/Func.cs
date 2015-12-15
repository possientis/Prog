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


  public static Func<X, Z> Compose<X, Y, Z>(
      Func<X, Y> f,
      Func<Y, Z> g
  ){
    return x => g(f(x));
  }

  public static void Main(string[] args)
  {
    Func<int, long> cube = x => (long) x*x*x;
    Func<long, double> halve = y => y / 2.0;
    Func<int, double> both = Compose(cube, halve);

    Func<int, Nullable<double>> log = x => x > 0 ?
      new Nullable<double>(Math.Log(x)) : new Nullable<double>();

    Func<double, Nullable<decimal>> toDecimal = 
      y => Math.Abs(y) < (double) decimal.MaxValue ? 
        new Nullable<decimal>((decimal) y) :
        new Nullable<decimal>();




    Console.WriteLine(both(2));
    Console.WriteLine(log(8)/log(2));

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
 
