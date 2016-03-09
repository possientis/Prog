// A storming performance from Java which even beats Haskell on large input

// We did not implement memoization in the thunk. We initially forgot,
// then realized it had no beneficial impact in the Scheme implementation

@FunctionalInterface
interface Thunk<T> {
  public Cell<T> run();
}

@FunctionalInterface
interface Predicate<T> {
  public boolean eval(T t);
}

@FunctionalInterface
interface Transition<T> {
  public T next(T t);
}

// parameterized predicate (e.g. n % x != 0 ). This allows the 'sieve' trick
// for prime numbers to be generically defined, rather than specialized to Integer
@FunctionalInterface
interface ParamPredicate<T> {
  public boolean eval(T t, T param);
}

// quick and dirty implementation of infinite streams
// (which can be finite). We have not defined the empty stream.
class Cell<T> {
  private final T car;
  private Thunk<T> cdr;
  private Cell(T first, Cell<T> rest){
    this.car = first;
    this.cdr = () -> rest;  // anonymous class implementing Thunk<T> is created
  } 

  public T first() { return car; }
  public Cell<T> rest() { return cdr.run(); }

  public Cell<T> filter(Predicate<T> p){
    Cell<T> next = this;
    while(!p.eval(next.first())){
      next = next.rest();
    }
    final Cell<T> succeed = next;  // cannot capture non final reference in lambda
    Cell<T> cell = new Cell<T>(succeed.first(), null);
    cell.cdr = () -> succeed.rest().filter(p);
    return cell;
  }

  public Cell<T> take(int N){
    assert(N > 0);
    Cell<T> cell = new Cell<>(first(), null);
    if(N == 1) return cell;
    cell.cdr = () -> rest().take(N-1);
    return cell;
  }


  // danger if stream is infinite, use take
  @Override
  public String toString(){
    String str = "(";
    Cell<T> next = this;
    while(next != null){
      str += next.first() + " ";
      next = next.rest(); // should be null at some point if finite stream
    }
  return str + "\b)";
  }
  
  // produces infinite stream from initial vallue and transition function
  public static <T> Cell<T> fromTransition(T init, Transition<T> f){
    Cell<T> cell = new Cell<>(init, null);
    cell.cdr = () -> fromTransition(f.next(init),f);
    return cell;
  }


  public static <T> Cell<T> sieve(Cell<T> input, ParamPredicate<T> p){
    T x = input.first();
    Cell<T> cell = new Cell<>(x,null);
    cell.cdr = () -> sieve(input.rest().filter(n -> p.eval(n,x)), p);
    return cell;
  }
}


public class Primes {
  public static void main(String[] args){
    int numPrimes = Integer.parseInt(args[0]);
    Cell<Integer> from2 = Cell.fromTransition(2, n -> n+1);
    Cell<Integer> primes = Cell.sieve(from2, (n,x) -> n % x != 0);
    System.out.println(primes.take(numPrimes));
  }
}
