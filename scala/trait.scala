// one major use of trait: turning a thin interface into a thick one




// example of a simple trait
trait Printable {
  def print() {
    println(this)
  }
}

// trait can be inherited from like an interface
// with default implementation

// using the keyword 'with'
class Frog extends Object with Printable {
  override def toString = "a frog"
}


val frog = new Frog
frog.print()

// equivalent code
class Frog2 extends Printable {
  override def toString = "a frog"
}

val frog2 = new Frog2
frog2.print()

// a trait cannot have any class parameters
// however a trait can have data, see below 'HashCashing'
class Point(x: Int, y: Int){
} // this is fine

// this will not compile
//trait NoPoint(x:Int, y:Int){
//  }

// traits are very useful to add methods to a class
// in terms of methods the class already has. In other words
// it is useful to extend a thin interface of primitive 
// methods into a thick interface

//"To use traits as interface thickeners, simply define a trait with a small
//number of abstract methods—the thin part of the trait’s interface—and a
//potentially large number of concrete methods, all implemented in terms of
//the abstract methods. Then you can take any class implementing the thin
//version of the interface, mix in the thickening trait, and end up with a class
//that has all of the thick interface available."


// what you would write without traits
class Book(val author: String, val title: String) {
  def <(that: Book) =
    (author < that.author) ||
    ((author == that.author) && title < that.title)
  def >(that: Book) = that < this
  def <=(that: Book) = (this < that) || (this == that)
  def >=(that: Book) = (this > that) || (this == that)
  override def equals(that: Any) =
    that match {
    case that: Book =>
      (author == that.author) && (title == that.title)
    case _ => false
  }
}

// you cannot put 'equals' inside the trait
trait Ordered[T] {
  def compare(that: T): Int
  def <(that: T): Boolean = (this compare that) < 0
  def >(that: T): Boolean = (this compare that) > 0
  def <=(that: T): Boolean = (this compare that) <= 0
  def >=(that: T): Boolean = (this compare that) >= 0
}

class Book2(val author: String, val title: String)
extends Ordered[Book2]
{
  def compare(that: Book2): Int =
    if (author < that.author) -1
    else if (author > that.author) 1
    else if (title < that.title) -1
    else if (title > that.title) 1
    else 0
// you still need to override equals, which cannot be
// part of the Ordered trait itself
  override def equals(that: Any) =
    that match {
      case that: Book2  => compare(that) == 0
      case _ => false
  }
}

//////////////////////////////////////////////////////////////////////
// modifying a class with traits: feels like the decorator pattern  //
//////////////////////////////////////////////////////////////////////
// caching hashCode 
trait HashCaching {
  /** A cache holding the computed hash. */
  private var cachedHash: Int = 0
  /** A boolean indicating whether the cache is defined */
  private var hashComputed: Boolean = false
  /** The hash code computation is abstract */
  def computeHash: Int
  /** Override the default Java hash computation */
  override def hashCode = {
    if (!hashComputed) {
      cachedHash = computeHash
      hashComputed = true
    }
      cachedHash
    }
}


class Book3(val author: String, val title: String)
extends Ordered[Book3]
with HashCaching
{
  // compare and equals as before
  def compare(that: Book3): Int =
    if (author < that.author) -1
    else if (author > that.author) 1
    else if (title < that.title) -1
    else if (title > that.title) 1
    else 0
// you still need to override equals, which cannot be
// part of the Ordered trait itself
  override def equals(that: Any) =
    that match {
      case that: Book3  => compare(that) == 0
      case _ => false
  }
 
  def computeHash = author.hashCode + title.hashCode

}

// this creates a problem....
trait HashCaching2 {
  private var cachedHash: Int = 0
  private var hashComputed: Boolean = false
  /** Override the default Java hash computation */
  override def hashCode = {
    if (!hashComputed) {
      cachedHash = super.hashCode
      hashComputed = true
    }
  cachedHash
  }
}

// ... because class overrides hashCode
class Book4(val author: String, val title: String)
extends Ordered[Book4]
with HashCaching2
{
  // compare and equals() as before...
  def compare(that: Book4): Int =
    if (author < that.author) -1
    else if (author > that.author) 1
    else if (title < that.title) -1
    else if (title > that.title) 1
    else 0
// you still need to override equals, which cannot be
// part of the Ordered trait itself
  override def equals(that: Any) =
    that match {
      case that: Book4  => compare(that) == 0
      case _ => false
  }

  override def hashCode = {
    Thread.sleep(3000) // simulate a VERY slow hash
    author.hashCode + title.hashCode
  }
}

// possible solution
abstract class BaseBook(val author: String, val title: String)
{
  override def hashCode = {
  Thread.sleep(3000)
  author.hashCode + title.hashCode
  }
}

// hashCode from HashCaching2 is not overriden
class Book5(author: String, title: String)
extends BaseBook(author, title)
with Ordered[Book5]
with HashCaching2 {
  // compare and equals() as before...
  def compare(that: Book5): Int =
    if (author < that.author) -1
    else if (author > that.author) 1
    else if (title < that.title) -1
    else if (title > that.title) 1
    else 0
  // you still need to override equals, which cannot be
  // part of the Ordered trait itself
  override def equals(that: Any) =
    that match {
      case that: Book5  => compare(that) == 0
      case _ => false
  }
}

trait HashScrambling
{
  override def hashCode = {
    val original: Int = super.hashCode
    def rl(i: Int) = Integer.rotateLeft(original, i)
// this line fails, not sure why
//    original ˆ rl(8) ˆ rl(16) ˆ rl(24)
  }
}



