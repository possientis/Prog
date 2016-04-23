// IndexedSeq is a trait, which the String class does not extend (implement).
// However, you can define an implicit conversion function from String
// to the trait IndexedSeq

// had to use 'my...' or 'My..' for this to compile, as scala
// defines some implicit conversion between String and traits
// which support an 'exist' method

trait MyIndexedSeq[T] extends IndexedSeq[T] {
  def myExists(p: T => Boolean) : Boolean = exists(p) 
}

implicit def myStringWrapper(s: String) = 
  new MyIndexedSeq[Char] {
    def length = s.length
    def apply(i:Int) = s.charAt(i)
  }

// then you can use a string object, as if it was an IndexedSeq
println("abc" myExists ('c' == _))


// Other example
// Haskell typeclass Show
trait Show {
  def show : String
}

// instance Show String where
//   show s =  s


implicit def toShow(s: String) = 
  new Show {
    def show = s
  }

println("abc" show)

// normally conversion function should be referenced
// with a single identifier, nothing like foo.XToY...

// There is one exception, when part of companion object
// of source or target type
object X {
  implicit def XToY(x: Y) = null
}

object Y {
  implicit def YToX(y:Y) = null
}

class Y {}
class X {}


// if application inherit from trait, then conversion function
// will be accessible 'as single identifier' and implicit
// conversion can occur
import javax.swing._
trait GUIFramework {
  implicit def stringToLabel(s: String): JLabel = new JLabel(s)
}

trait WindowsFramework extends GUIFramework {
  val WindowsLabelUI = null
  implicit override def stringToLabel(s: String): JLabel = {
    val label = super.stringToLabel(s)
    label setUI WindowsLabelUI
    label
  }
}

// THERE ARE 3 CASES OF IMPLICIT CONVERSION

// 1. Implicit conversion to an expected type
// compiler sees an X but needs a Y, looking for implicit from X to Y.

//val i:Int = 3.5  // failing, but ...

implicit def double2int(x: Double) = x.toInt
val i:Int = 3.5 // fine now
println(i)  // 3


// 2. Converting the receiver
// compiler sees foo.doIt while foo does not have a 'doIt' method.
// will look for implicit conversion to a type with a 'doIt' method
// (it should be unique as no implicit conversion occurs when ambiguous)

// This has has two major application:
// 2.a it provides support to defining a new type

class Rational(n:Int, d:Int){
  def+(that:Rational):Rational = null
  def+(that:Int):Rational = null
}

// so Rational + Rational and Rational + Int will work fine
// but what about Int + Rational?
implicit def IntToRationa(x:Int) = new Rational(x,1)
// now Int + Rational will work too


// 2.b it allows the simulation of 'adding new syntax'
// with the 'RichFoo' pattern. You have a Foo class 
// which doed not have an infix -> operator. You create
// a RichFoo class where -> is defined and you define
// an implicit conversion from Foo to RichFoo

val m = Map(1->"one", 2->"two", 3->"three")

// there is a class RichAny with a -> method
// and there is a conversion from Any to RichAny

// 3. Implicit parameters

def printSomething(implicit x: Int) = println(x)

// can be called like any other function
printSomething(10)  // 10

implicit val favouriteNumber = 4

printSomething      // 4

def maxList[T](nums: List[T])(implicit orderer: T=>Ordered[T]): T =
  nums match {
    case List()   => throw new Error("empty lists!")
    case List(x)  => x
    case x::rest  =>
      val maxRest = maxList(rest)(orderer)
      if (orderer(x) > maxRest) x
      else maxRest
    }

println(maxList(List(1,5,10,3)))              // 10
println(maxList(List(1.5,5.2,10.7,3.14159)))  //10.7

def maxList2[T](nums: List[T])(implicit orderer: T=>Ordered[T]): T = 
  nums match {
    case Nil      => throw new Error("empty list!")
    case List(x)  => x
    case x::rest  => 
      val maxRest = maxList2(rest)  // (orderer) is redundant
      if(x > maxRest) x             // orderer(x) is redundant
      else  maxRest
  }

// the name 'orderer' does not appear anywhere in the body of maxList2
// in fact this name could be changed to anything

// note the distinction between '<%' and '<:' we are not saying that
// type T should be a subtype of Ordered[T]. We are saying it can be 
// as an Ordered[T] (it is up to the user to supply a conversion)
// the compiler will provide the identity as conversion. So if T is
// already an Ordered[T], there is no need to worry about the need
// to spell out a conversion
def maxList3[T<% Ordered[T]](nums: List[T]): T = 
  nums match {
    case Nil      => throw new Error("empty list!")
    case List(x)  => x
    case x::rest  => 
      val maxRest = maxList2(rest)  // (orderer) is redundant
      if(x > maxRest) x             // orderer(x) is redundant
      else  maxRest
  }
  



