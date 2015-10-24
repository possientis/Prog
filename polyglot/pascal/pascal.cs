using System;
using System.Collections.Generic;
using System.Linq;

public class Pascal{

  private static IList<int> NewList(){
    // choice of IList<T> implementation goes here 
    return new List<int>();
  }

  public static IList<int> SlowPascal(int n){
    if(n == 1){
      IList<int> list = NewList();
      list.Add(1);
      return list;
    }
    else{
      return AddList(ShiftLeft(SlowPascal(n - 1)),ShiftRight(SlowPascal(n - 1)));
    }
  }

  public static IList<int> FastPascal(int n){
    if(n == 1){
      IList<int> list = NewList();
      list.Add(1);
      return list;
    }
    else{
      IList<int> list = FastPascal(n - 1);
      return AddList(ShiftLeft(list),ShiftRight(list));
    }
  }

  public static IList<int> ShiftLeft(IList<int> list){
    IList<int> temp = NewList();
    foreach(int i in list) temp.Add(i);
    temp.Insert(0,0);
    return temp;
  }

  public static IList<int> ShiftRight(IList<int> list){
    IList<int> temp = NewList();
    foreach(int i in list) temp.Add(i);
    temp.Add(0);
    return temp;
  }
    
  public static IList<int> AddList(IList<int> list1, IList<int> list2){
    IList<int> temp = NewList();
    IEnumerator<int> iter1 = list1.GetEnumerator();
    IEnumerator<int> iter2 = list2.GetEnumerator();
    while(iter1.MoveNext() != false){
      iter2.MoveNext();
      temp.Add(iter1.Current + iter2.Current);
    }
    return temp; 
  }

  // don't have a better idea right now
  public static void show(IList<int> list){

    bool start = true;
    foreach(int i in list){
      Console.Write(start ? '[': ',');
      start = false;
      Console.Write(i);
    }
    Console.WriteLine(']');

  }

  public static void Main(string[] args){
    IList<int> list = FastPascal(20);
    show(list);
  }


}

