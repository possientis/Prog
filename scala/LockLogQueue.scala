// using traits, decorator pattern
trait Queue {
  def get(): Int
  def put(x: Int)
}

// first point:
// locking and logging traits specify queue
// as superclass. Any class they are mixed into
// must be a subtype of Queue

// second point:
// these traits make super calls on methods
// which are declared abstract !!! Such
// calls are illegal for normal classes.
// For a trait, such call can succeed so 
// long as the trait is mixed after 
// another trait which gives a concrete 
// definition to the method.
// you tell the compiler with 'abstract
// override', a combination of modifiers
// which normally makes no sense


// there is a big difference between super 
// calls in traits and in classes.
// for classes, super calls invoke a known
// method, while in a trait, the method is
// different for each place in the code the
// trait is mixed in


// traits are not the same as multiple inheritance
// found in other languages, due to the different
// meaning of super calls.



// decorate queue with synchronization
trait LockingQueue extends Queue {
  abstract override def get(): Int =
    // btw scala supports synchronized blocks to make a region of code atomic
    // unlike java, there is no synchronized method modifier
    synchronized { super.get() }
  abstract override def put(x: Int) =
    synchronized { super.put(x) }
}

// decorate queue with logging
trait LoggingQueue extends Queue {
  def log(message: String) = println(message)
  abstract override def get(): Int = {
    val x = super.get()
    log("got: " + x)
    x
  }
  abstract override def put(x: Int) {
    super.put(x)
    log("put: " + x)
  }
}


import scala.collection.mutable.ArrayBuffer
class StandardQueue extends Queue {
  private val buf = new ArrayBuffer[Int]
  def get = buf.remove(0)
  def put(x: Int) = buf += x
}

val q1 = new StandardQueue with LockingQueue with LoggingQueue
val q2 = new StandardQueue with LoggingQueue


