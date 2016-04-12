// functional queue: head, tail, enqueue, dequeue
import scala.collection.immutable.Queue
val q = Queue(1, 2, 3)
println(q)  // Queue(1, 2, 3)
val q1 = q enqueue 4
println(q1) // 
val a = q1.dequeue
println(a)  // (1,Queue(2, 3, 4)) 
println(q1) // Queue(1, 2, 3, 4)


// naive implementation of immutable queue as list
class Queue1[T](elems: List[T]) {
  def head = elems.head
  def tail = elems.tail
  def enqueue(x: T) = new Queue1(elems ::: List(x))
  override def toString = elems.toString
}

val q2 = new Queue1[Int](List(1,2,3,4,5))
println(q2) // List(1, 2, 3, 4, 5)
val q3 = q2 enqueue 6
println(q3) // List(1, 2, 3, 4, 5, 6)

// problem ----> append (enqueue) has linear complexity, not constant


// functional queues. 
class Queue2[T] private (val leading: List[T], val trailing: List[T]) { // private primary constructor

  def this() = this(Nil, Nil)                 // creating secondary constructor
  def this(elems: List[T]) = this(elems, Nil) // creating secondary constructor
//  def this(elems: T*) = this(elems.toList, Nil) // variable number of arguments but failing
  // define an object Queue2 with an apply method (see below)

  private def mirror =
    if (leading.isEmpty) new Queue2(trailing.reverse, Nil)
    else this

  def head = mirror.leading.head

  def tail = {
    val q = mirror;
    new Queue2(q.leading.tail, q.trailing)
  }

  def enqueue[T](x: T) = new Queue2(leading, x :: trailing)
  
  // dequeue?
  
  override def toString = (leading ++ trailing.reverse).toString
}

// same file -> becomes companion object of class, with same access rights
// so apply can access primary constructor eventhough it is private
// There is no such things as global method in scala (they are all within classes or objects)
// but using object makes it look like Queue2 is a global factory method
object Queue2 {
  def apply[T](xs: T*) = new Queue2[T](xs.toList, Nil)  // variable number of arguments '*'
}

val q4 = Queue2()
println(q4) // List()

val q5 = Queue2(3)
println(q5) // List(3)

val q6 = Queue2(5,7)
println(q6) // List(5, 7)


// even better, using the bridge design pattern

trait Queue3[T] {
  def enqueue(x:T) : Queue3[T]
  def dequeue()    : (T, Queue3[T]) 
}

object Queue3 {
  def apply[T](xs: T*) : Queue3[T] = // variable number of arguments
    new QueueImpl(xs.toList, Nil)

    private class QueueImpl[T](val leading: List[T], val trailing: List[T])
      extends Queue3[T] {  // private inner class (nested class)
      
      def normalize = 
        if(leading.isEmpty)
          new QueueImpl(trailing.reverse, Nil)
        else
          this
      def enqueue(x:T) = new QueueImpl(leading, x::trailing)
      def dequeue() = {
        val q = normalize
        (leading.head, new QueueImpl(leading.tail, trailing))
      }
    }
}





  




