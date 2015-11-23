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

class Program
{

  static void Main(string[] args)
  {
    A a1 = new A("john", 3000);
    A a2 = new A("paul", 2000);
    A a3 = new A("luke", 4000);
    A a4 = new A("matt",1000);
    
    Queue<A> q = new Queue<A>();

    q.Enqueue(a1);
    q.Enqueue(a2);
    q.Enqueue(a3);
    q.Enqueue(a4);

    ShowQueue(q);

    A a = q.Dequeue();
    Console.WriteLine("{0} has been removed",a.Name);

    ShowQueue(q);

  }

  public static void ShowQueue(Queue<A> q){
    foreach(A a in q){
      Console.WriteLine("Name = {0}, Salary = {1}", a.Name,a.Salary);
    }

  }

}

class A{
  public A(string name, int salary){Name = name; Salary = salary;}
  public string Name {get; set;}
  public int Salary {get; set;}
  
}


      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
