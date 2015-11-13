using System;
using System.IO;  // StreamReader
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;


using System.Reflection;

class Program
{

  static void Main(string[] args)
  {


    //Type T = Type.GetType("A");
    Type T = typeof(A); // quicker
    Console.WriteLine("FullName = {0}", T.FullName);
    Console.WriteLine("Just the Name = {0}", T.Name);
    Console.WriteLine("Namespace = {0}", T.Namespace);



    Console.WriteLine("Properties:");
    PropertyInfo[] props = T.GetProperties();
    foreach(PropertyInfo prop in props){
      Console.WriteLine(prop.Name + ":" + prop.PropertyType.Name + ":" + prop.ToString());
    }

    Console.WriteLine("Methods:");
    MethodInfo[] meths = T.GetMethods();
    foreach(MethodInfo meth in meths){
      Console.WriteLine(meth.Name + ":" + meth.ReturnType.Name + ":" + meth.ToString());
    }

    Console.WriteLine("Constructors:");
    ConstructorInfo[] cons = T.GetConstructors();
    foreach(ConstructorInfo con in cons){
      Console.WriteLine(con.ToString());
    }



  }
}

class A{
  private int a;

  public A(int a){this.a = a;}

  public int B{
    get{return a;}
    set{a = value;}
  }
  public int get(){return a;}

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
 
