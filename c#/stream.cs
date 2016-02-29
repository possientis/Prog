using System;
using System.Collections.Generic;

public delegate Cell<T> Thunk<T>();
public delegate T Transition<T>(T t);
public delegate bool Predicate<T>(T t);
public delegate bool ParamPredicate<T>(T t, T param);

public class Cell<T> {
  private readonly T car;
  private Thunk<T> cdr;
  private Cell(T first, Cell<T> rest){
    this.car = first;
    this.cdr = new Thunk<T>(() => rest);
  }
  public T First {
    get { return car; }
  }
  public Cell<T> Rest{
    get { return cdr(); }
  }
  
  public Cell<T> Filter(Predicate<T> p){
    Cell<T> next = this;
    while(!p(next.First)){
      next = next.Rest;
    }
    Cell<T> cell = new Cell<T>(next.First, null);
    cell.cdr = new Thunk<T>(() => next.Rest.Filter(p));
    return cell;
  }

  public static Cell<T> Cons(T first, Cell<T> rest){
    Cell<T> cell =  new Cell<T>(first, rest);
    return cell;
  }
  public static Cell<T> FixPoint(T elem){
    Cell<T> cell = new Cell<T>(elem,null);
    cell.cdr = new Thunk<T>(() => cell);
    return cell;
  }

  public static Cell<T> FromIEnumerator(IEnumerator<T> list){
    list.MoveNext();
    Cell<T> cell = new Cell<T>(list.Current,null);
    cell.cdr = new Thunk<T>(()=> FromIEnumerator(list));
    return cell;
  }

  public static Cell<T> FromIEnumerable(IEnumerable<T> list){
    return FromIEnumerator(list.GetEnumerator());
  }

  public static Cell<T> FromTransition(T init, Transition<T> f){
    Cell<T> cell = new Cell<T>(init, null);
    cell.cdr = new Thunk<T>(()=> FromTransition(f(init),f));
    return cell;
  }

  public void Display(int N){
    int count = 0;
    Cell<T> next = this;
    Console.Write("[");
    while(count < N){
      count++;
      Console.Write(next.First);
      Console.Write(",");
      next = next.Rest;
    }
    if(count > 0){
      Console.Write("\b");
    }
    Console.Write("]\n");
  }

  public static Cell<T> Sieve(Cell<T> input, ParamPredicate<T> p){
    T x = input.First;
    Cell<T> cell = new Cell<T>(x, null);
    cell.cdr = new Thunk<T>(() => Sieve(input.Rest.Filter((T n) => p(n,x)), p));
    return cell;
  }

}


class Program {
  public static void Main(string[] args){
    Cell<int> from2 = Cell<int>.FromTransition(2,(int n) => n+1);
    Cell<int> primes = Cell<int>.Sieve(from2, (n,x) => n % x != 0); 
    primes.Display(1000);
  }



}
