// some implementations are not tail recursive, and do not reflect
// the exact details of scala 'List[T]' implementation (which is tail-recursive)
// use ListBuffer (+= method to add element and then toList method, both constant time)
// with ListBuffer you can incremental add elements as the end
abstract class MyList[+T]{  // covariant
  def isEmpty:Boolean
  def head: T
  def tail: MyList[T] 
  // method ending with a colon -> x::xs is xs.::(x)
  // i.e. such method binds to the right, and it is also right-associative
  def ::[U >: T](x:U): MyList[U] = new cons[U](x,this);     // works for U supertype of T
  def :::[U >: T](prefix: MyList[U]) : MyList[U] =          // concat , append 
    if(prefix.isEmpty) this
    else prefix.head::prefix.tail:::this  // (these methods are right associative)
  def length : Int = if (isEmpty) 0 else 1 + tail.length
  def toList : List[T] = if(isEmpty) Nil else head::tail.toList
}
// override modifier seems optional everywhere

// Nil is case object, not case class
// covariance means it will work for all T's
case object MyNil extends MyList[Nothing] {
  override def isEmpty = true
  override def head: Nothing = 
    throw new NoSuchElementException("head of empty list")
  override def tail: MyList[Nothing] =
    throw new NoSuchElementException("tail of empty list")
}

// name '::' already taken
// no need to define head and tail, cons is case class, so implicitely
// define from constructor arguments
final case class cons[T](head:T, tail:MyList[T]) extends MyList[T] { 
  override def isEmpty: Boolean = false
}


val l = 1::2::3::MyNil
val m = 4::5::6::MyNil
val n = l:::m

println(l.toList)
println(m.toList)
println(n.toList)

