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

class Program
{

  static void Main(string[] args)
  {
    A a1 = new A("john", 3000);
    A a2 = new A("paul", 2000);
    A a3 = new A("luke", 4000);
    A a4 = new A("matt",1000);

    List<A> list = new List<A>();
    list.Add(a1);
    list.Add(a2);
    list.Add(a3);
    list.Add(a4);

    // Default sorting stemming from implementation of IComparable<A> innterface
    Console.WriteLine("List before sorting:");
    ShowList(list);
    list.Sort();  // default (no argument)
    Console.WriteLine("List after sorting:");
    ShowList(list);
    list.Reverse();
    Console.WriteLine("List after reversing order:");
    ShowList(list);

    // Sorting with an 'IComparer<A>' object
    IComparer<A> myComparer = new SortByName(); // see below, 'SortByName' implements 'IComparer<A>'
    list.Sort(myComparer);  // no longer the default sorting
    Console.WriteLine("List after alphabetical sorting:");
    ShowList(list);

    // Sorting with a delegate in the form of Comparison<A> object
    Comparison<A> comparer = new Comparison<A>(CompareA);
    list.Sort(comparer);
    Console.WriteLine("List after reverse alphabetical sorting:");
    ShowList(list);
   

    // Even quicker using delegate
    list.Sort(delegate(A x, A y){return x.Name.CompareTo(y.Name);});
    Console.WriteLine("List after alphabetical sorting:");
    ShowList(list);

    // You cannot beat lambda
    list.Sort((x,y) => y.Name.CompareTo(x.Name));
    Console.WriteLine("List after reverse alphabetical sorting:");
    ShowList(list);
 
  }

  public static void ShowList(List<A> list){
    foreach(A a in list){
      Console.WriteLine("Name = {0}: Salary = {1}", a.Name,a.Salary);
    }
  }

  public static int CompareA(A x, A y){
    return y.Name.CompareTo(x.Name);  // reverse alphabetical order
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

// However, it may be that default sorting is not what we want. Need to create a concrete 'IComparer<A>'
class SortByName : IComparer<A> {
  public int Compare(A x, A y){
    return x.Name.CompareTo(y.Name);
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
 
