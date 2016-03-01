using System;
using System.Collections.Generic;

public delegate Cell<T> Thunk<T>();
public delegate T Transition<T>(T t);
public delegate bool Predicate<T>(T t);
public delegate bool ParamPredicate<T>(T t, T param);

public class Cell<T> {
  private static long timer = 0;
  public static void ResetTimer(){
    timer = 0;
  }
  public static void PrintTime(){
    Console.WriteLine("Time = " + timer);
  }
  private readonly T car;
  private Thunk<T> cdr;
  private Cell(T first, Cell<T> rest){
    this.car = first; timer++;
    this.cdr = new Thunk<T>(() => rest); timer++;
  }
  public T First {
    get { timer++; return car; }
  }
  public Cell<T> Rest{
    get { timer++; return cdr(); }
  }
  
  public Cell<T> Filter(Predicate<T> p){
    Cell<T> next = this; timer++;
    while(!p(next.First)){
      next = next.Rest; timer++;
    }
    Cell<T> cell = new Cell<T>(next.First, null); timer++;
    cell.cdr = new Thunk<T>(() => next.Rest.Filter(p)); timer++;
    return cell;
  }

  public static Cell<T> Cons(T first, Cell<T> rest){
    Cell<T> cell =  new Cell<T>(first, rest); timer++;
    return cell;
  }

 public static Cell<T> FromTransition(T init, Transition<T> f){
    Cell<T> cell = new Cell<T>(init, null); timer++;
    cell.cdr = new Thunk<T>(()=> FromTransition(f(init),f));timer++;
    return cell;
  }

  public void Display(int N){
    int count = 0; timer++;
    Cell<T> next = this; timer++;
    Console.Write("["); timer++;
    while(count < N){
      count++; timer++;
      Console.Write(next.First); timer++;
      Console.Write(","); timer++;
      next = next.Rest;timer++;
    }
    if(count > 0){
      Console.Write("\b"); timer++;
    }
    Console.Write("]\n"); timer++;
  }

  public static Cell<T> Sieve(Cell<T> input, ParamPredicate<T> p){
    T x = input.First; timer++;
    Cell<T> cell = new Cell<T>(x, null); timer++;
    cell.cdr = new Thunk<T>(() => Sieve(input.Rest.Filter((T n) => p(n,x)), p));
    timer++;
    return cell;
  }
}


class Program {
  public static void Main(string[] args){
    Cell<int>.ResetTimer();
    Cell<int>.PrintTime();
    Cell<int> from2 = Cell<int>.FromTransition(2,(int n) => n+1);
    Cell<int> primes = Cell<int>.Sieve(from2, (n,x) => n % x != 0); 
    primes.Display(1000);
    Cell<int>.PrintTime();
  }



}
