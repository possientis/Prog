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


  private static IEnumerable<int> FromTwo(){
    for(int i = 2;;){
      yield return i++;
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

  public static IEnumerable<int> FromEnumerator(IEnumerator<int> iter){
    while(iter.MoveNext() != false){
      int t = iter.Current;
      yield return t;
    }
  }
  

  public static IEnumerable<int> Filter(IEnumerable<int> input, Predicate<int> p){
    IEnumerator<int> iter = input.GetEnumerator();
    while(iter.MoveNext() != false){
      int t = iter.Current;
      if(p(t)){
        yield return t;
      }
    }
  }


  public static IEnumerable <int> Sieve (IEnumerable<int> input){
     int x = First(input); 
     yield return x;
     IEnumerable<int> rest = Sieve(Filter(Rest(input), (int n) => n % x != 0));
     foreach(int n in rest){
       yield return n;
     }
  }

  public static void Main(string[] args){
    int numPrimes = Int32.Parse(args[0]);
    ResetTimer();
    PrintTime();
    IEnumerable<int> primes = Sieve(FromTwo());
    Display(primes, numPrimes);
    PrintTime();
  }

}
