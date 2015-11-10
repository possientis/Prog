using System;
using System.IO;  // StreamReader
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

class Program
{
  public enum Gender {MALE=4,FEMALE=23,UNKNOWN=45};

  static void Main(string[] args)
  {
    // 'Enum' is a class... do not confuse it with keyword 'enum'
    int[] x = (int[]) Enum.GetValues(typeof(Gender));
    foreach(int y in x){
      Console.WriteLine(y);
    }

    string[] names = (string []) Enum.GetNames(typeof(Gender));
    foreach(string s in names){
      Console.WriteLine(s);
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
 
