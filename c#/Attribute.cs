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

  static void Main(string[] args)
  {

    int x = 2;
    int y = 3;
    int z = 4;

    int t = A.Add(x,y,z);
    
    Console.WriteLine(t);

  }
}

class A{
  public static int Add(int x, int y){

    return x + y;

  }

  // Attributes are classes derived from Attribute
  // the name of the class is actually 'ObsoleteAttribute'
  [Obsolete("It is recommended you use A.Add(x,y)")] // will generate compiler warning
  public static int Add(int x, int y, int z){
    return x + y + z;

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
 
