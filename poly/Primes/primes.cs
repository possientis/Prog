// We did not implement memoization in the thunk. We initially forgot,
// then realized it had no beneficial impact in the Scheme implementation

using System;
using System.Diagnostics;
using System.Collections.Generic;

delegate Cell<T> Thunk<T>();

public delegate T Transition<T>(T t);

public delegate bool Predicate<T>(T t);
//
// parameterized predicate (e.g. n % x != 0 ). This allows the 'sieve' trick
// for prime numbers to be generically defined, rather than specialized to Integer
public delegate bool ParamPredicate<T>(T t, T param);

// quick and dirty implementation of infinite streams
// (which can be finite). We have not defined the empty stream.
class Cell<T> {

  private readonly T car;
  private Thunk<T> cdr;

  private Cell(T first, Cell<T> rest){
    this.car = first;
    this.cdr = new Thunk<T>(() => rest); 
  }

  public T First { get { return car; } }
  public Cell<T> Rest{ get {  return cdr(); } }
  
  public Cell<T> Filter(Predicate<T> p){
    Cell<T> next = this;
    while(!p(next.First)){
      next = next.Rest;
    }
    Cell<T> cell = new Cell<T>(next.First, null); 
    cell.cdr = new Thunk<T>(() => next.Rest.Filter(p));
    return cell;
  }


  // produces infinite stream from initial value and transition function
  public static Cell<T> FromTransition(T init, Transition<T> f){
    Cell<T> cell = new Cell<T>(init, null); 
    cell.cdr = new Thunk<T>(() => FromTransition(f(init),f));
    return cell;
  }

  public Cell<T> Take(int N){
    Debug.Assert(N > 0);
    Cell<T> cell = new Cell<T>(First, null);
    if(N == 1) return cell;
    cell.cdr = new Thunk<T>(() => Rest.Take(N-1));
    return cell;
  }

  // danger if stream is infinite, use Take
  public override string ToString(){
    string str = "(";
    Cell<T> next = this;
    while(next != null){
      str += next.First + " ";
      next = next.Rest; // should be null at some point if finite stream
    }
    return str + "\b)";
  }

  public static Cell<T> Sieve(Cell<T> input, ParamPredicate<T> p){
    T x = input.First;  
    Cell<T> cell = new Cell<T>(x, null); 
    cell.cdr = new Thunk<T>(() => Sieve(input.Rest.Filter((T n) => p(n,x)), p));
    return cell;
  }
}


public class Primes {
  public static void Main(string[] args){
    int numPrimes = Int32.Parse(args[0]);
    Cell<int> from2 = Cell<int>.FromTransition(2,(int n) => n+1);
    Cell<int> primes = Cell<int>.Sieve(from2, (n,x) => n % x != 0);
    Console.WriteLine(primes.Take(numPrimes));
  }
}
