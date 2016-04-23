abstract class MyList[+T]{  // covariant
  def isEmpty:Boolean
  def head: T
  def tail: MyList[T]
}
// override modifier seems optional everywhere

// Nil is case object, not case class
// covariance means it will work for all T's
case object Nil extends MyList[Nothing] {
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
