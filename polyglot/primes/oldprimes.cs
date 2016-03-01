using System;
using System.Collections.Generic;



public delegate bool Predicate<T>(T t);

class Program {

  private static long timer = 0;

  public static void ResetTimer(){
    timer = 0;
  }
  public static void PrintTime(){
    Console.WriteLine("Time = " + timer);
  }

  public static void Main(string[] args){
    ResetTimer();
    PrintTime();
    IEnumerable<int> primes = Sieve(FromTwo());
    Display(primes, 1000);
    PrintTime();
  }


  public static IEnumerable <int> Sieve (IEnumerable<int> input){
     int x = First(input); timer++;
     yield return x; timer++;
     IEnumerable<int> rest = Sieve(Filter(Rest(input), (int n) => n % x != 0)); timer++;
     foreach(int n in rest){
       yield return n; timer++;
     }
  }

  private static IEnumerable<int> FromTwo(){
    for(int i = 2;;){
      yield return i++; timer++;
    }
  }

  public static IEnumerable<int> Filter(IEnumerable<int> input, Predicate<int> p){
    foreach(int t in input){
      if(p(t)) yield return t; timer++;
    }
  }

  public static int First(IEnumerable<int> input){
    IEnumerator<int> iter = input.GetEnumerator(); timer++;
    iter.MoveNext(); timer++;
    return iter.Current;
  }

  public static IEnumerable<int> Rest(IEnumerable<int> input){
    IEnumerator<int> iter = input.GetEnumerator(); timer++;
    iter.MoveNext(); timer++;
    while(true){
      iter.MoveNext();timer++;
      yield return iter.Current;timer++;
    }
  }

  public static void Display(IEnumerable<int> input, int N){
    IEnumerator<int> iter = input.GetEnumerator(); timer++;
    int count = 0; timer++;
    Console.Write("["); timer++;
    while(count < N){
      count++; timer++;
      iter.MoveNext(); timer++;
      Console.Write(iter.Current);timer++;
      Console.Write(",");timer++;
    }
    if(count > 0){
      Console.Write("\b"); timer++;
    }
    Console.Write("]\n"); timer++;
  }
}
