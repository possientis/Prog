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
