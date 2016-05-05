class A {
  def relation(other: Any):Boolean = {
    println("A::relation is running")
    true
  }
}

object A {
  def foo(a:A, B:A) = a relation b
}


class B extends A {
  override def relation(other: Any) = {
    println("B::relation is running")
    true
  }
}


val a = new A
val b = new B

a relation b  // A::relation is running
a relation a  // A::relation is running
b relation a  // B::relation is running
b relation b  // B::relation is running

val bb : A = new B

bb relation a // B::relation is running

A.foo(bb,a)   // B::relation is running


