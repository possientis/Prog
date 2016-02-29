using System;
using System.Collections.Generic;



public delegate bool Predicate<T>(T t);

class Program {

  public static void Main(string[] args){
    IEnumerable<int> primes = Sieve(FromTwo());
    Display(primes, 1000);
  }


  public static IEnumerable <int> Sieve (IEnumerable<int> input){
     int x = First(input);
     yield return x;
     IEnumerable<int> rest = Sieve(Filter(Rest(input), (int n) => n % x != 0));
     foreach(int n in rest)
       yield return n;
  }

  private static IEnumerable<int> FromTwo(){
    for(int i = 2;;){
      yield return i++;
    }
  }

  public static IEnumerable<int> Filter(IEnumerable<int> input, Predicate<int> p){
    foreach(int t in input){
      if(p(t)) yield return t;
    }
  }

  public static int First(IEnumerable<int> input){
    IEnumerator<int> iter = input.GetEnumerator();
    iter.MoveNext();
    return iter.Current;
  }

  public static IEnumerable<int> Rest(IEnumerable<int> input){
    IEnumerator<int> iter = input.GetEnumerator();
    iter.MoveNext();
    while(true){
      iter.MoveNext();
      yield return iter.Current;
    }
  }

  public static void Display(IEnumerable<int> input, int N){
    IEnumerator<int> iter = input.GetEnumerator();
    int count = 0;
    Console.Write("[");
    while(count < N){
      count++;
      iter.MoveNext();
      Console.Write(iter.Current);
      Console.Write(",");
    }
    if(count > 0){
      Console.Write("\b");
    }
    Console.Write("]\n");
  }
}
