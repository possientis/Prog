// We did not implement memoization in the thunk. We initially forgot,
// then realized it had no beneficial impact in the Scheme implementation

// quick and dirty implementation of infinite streams
// (which can be finite). We have not defined the empty stream.
class Cell[T](head: T, tail: Cell[T]){
  private val car = head
  private var cdr = () => tail
  def first = car
  def rest  = cdr()

  def filter(p: T => Boolean) : Cell[T] = {
    var next = this;
    while(!p(next.first)){
      next = next.rest
    }
    val succeed = next
    val cell = new Cell(succeed.first,null);
    cell.cdr = () => succeed.rest.filter(p)
    return cell
  }
  
  def take(N: Int) : Cell[T] = {
    assert(N > 0)
    val cell = new Cell(first, null)
    if(N == 1) return cell
    cell.cdr = () => rest.take(N-1)
    return cell 
  } 

  // should rewrite this in functional way
  override def toString  = {
    var str : String = "("
    var next = this;
    while(next != null){
      str += next.first + " "
      next = next.rest
    }
    str + "\b)";
  } 
}

object Cell{
  def fromTransition[T](init: T, f : T => T) : Cell[T] = {
    val cell = new Cell[T](init, null)
    cell.cdr = () => fromTransition(f(init),f)
    return cell
  }

  def sieve[T](input: Cell[T], p: (T,T) => Boolean): Cell[T] = {
    val x = input.first
    val cell = new Cell(x,null)
    cell.cdr = () => sieve(input.rest.filter(n => p(n,x)), p)
    return cell
  }
}

object Primes {
  def main(args: Array[String]){
    val numPrimes = args(0).toInt;
    val from2 = Cell.fromTransition[Int](2, n => n+1)
    val primes = Cell.sieve[Int](from2, (n,x) => n % x != 0)
    println(primes.take(numPrimes))
  }
}
