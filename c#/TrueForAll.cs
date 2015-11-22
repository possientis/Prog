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

    List<A> list = new List<A>(10); // excess capacity, see TrimExcess
    list.Add(a1);
    list.Add(a2);
    list.Add(a3);
    list.Add(a4);
    ShowList(list);
    // TrueForAll
    Console.WriteLine("All have salaries less than 5000: {0}", 
        list.TrueForAll(x => x.Salary < 5000));
    // AsReadOnly
    ReadOnlyCollection<A> readList = list.AsReadOnly();
    Console.WriteLine(readList.Count);
    // TrimExcess
    Console.WriteLine(list.Capacity);
    list.TrimExcess();
    Console.WriteLine(list.Capacity);


  }

  public static void ShowList(List<A> list){
    foreach(A a in list){
      Console.WriteLine("Name = {0}: Salary = {1}", a.Name,a.Salary);
    }
  }
}

// class A implements IComparable<A> interface and therefore provides default sorting functionality via Sort()
class A : IComparable<A> {
  public A(string name, int salary){Name = name; Salary = salary;}
  public string Name {get; set;}
  public int Salary {get; set;}

  public int CompareTo(A a){
    return Salary.CompareTo(a.Salary);  // 'int' implements IComparable<int>
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
 
