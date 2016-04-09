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
  def append(x: T) = new Queue1(elems ::: List(x))
  override def toString = elems.toString
}

val q2 = new Queue1[Int](List(1,2,3,4,5))
println(q2) // List(1, 2, 3, 4, 5)
val q3 = q2 append 6
println(q3) // List(1, 2, 3, 4, 5, 6)

// problem ----> append (enqueue) has linear complexity, not constant
