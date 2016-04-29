// == is declared final in class Any. Cannot be overriden
// simply override 'equals' if you need to change the 
// meaning of ==
// final def ==(other: Any) : Boolean = this.equals(other)


// common pitfalls that may cause inconsistent behavior of equals

// 1. Defining equals with the wrong signature
// 2. Changing equals without also changing hashCode
// 3. Defining equals in terms of mutable fields
// 4. Failing to define equals as an equivalence relation

// PITFALL: defining 'equals' with the wrong signature
class Point(val x: Int, val y:Int){

  /** an utterly wrong definition of Equals **/
  // this is not even an override, so doesnt affect ==
  // try to add 'override' qualifier and it will not compile
  def equals(other: Point): Boolean = {
//    println("running")
    this.x == other.x && this.y == other.y
  }

}
// WARNING:
// def ==(other: Point): Boolean // don't do this !!!
// Compiler will not let you redefine ==(other:Any):Boolean because
// it is declared 'final' in scala library. 
// defining ==(other: Point): Boolean will not generate compiler warning

val p1 = new Point(2,3)
val p2 = new Point(2,3)
val q  = new Point(1,2)

println(p1 equals p2)   // true
println(p1 equals q)    // false


println(p1 == p2)   // false !!!!!!!!! (equals not an override)
println(p1 == q)    // false

import scala.collection.mutable._
val coll = HashSet(p1)
println(coll contains p2) // false !!!!!!

val p2Any : Any = p2
println(p2 equals p2Any)  // true, but this is not using *our* equals
println(p1 equals p2Any)  // false !!!!!, but this is not *our* equals
// REMEMBER: overloading resolution in Scala and Java is based on *static* type
// it is not based on run-time type. (Most likely the same applies in C++, C#)
// Code has a call to a.m(x) where a:A and x:X.
// class A two methods m(x:X) and m(y:Y) declared where Y <: X.
// The compiler pick m(x:X) for a.m(x) if x declared as x:X.
// the fact that x maybe also of type Y at run-time makes not difference

// def equals(other: Any): Boolean   --> this ***is*** what needs to be overriden

class Point2(val x: Int, val y:Int){

  /** A better definition, but still not perfect */
  override def equals(other: Any): Boolean =  other match {
    case that: Point2 => this.x == that.x && this.y == that.y
    case _            => false 
  }

}
println("\nWith better definition ...")

val p3  = new Point2(2,3)
val p4  = new Point2(2,3)
val p5  = new Point2(1,2)

println(p3 equals p4)     // true
println(p3 equals p5)     // false


println(p3 == p4)     // true
println(p3 == p5)     // false

val coll2 = HashSet(p3)
println(coll2 contains p4)  // false !!!, this is still not right   

// PITFALL : changing 'equals' without changing 'hashCode'

// AXIOM of 'hashCode': x == y => hashCode(x) == hashCode(y)
// (hashCode should be compatible with the relation == , and
// we shoould also make sure == is an equivalence relation)
// by overriding equals(other:Any) without overriding hashCode(),
// we broke the requirement of the axiom

class Point3(val x: Int, val y:Int){

  /** A proper implementation, without forgetting hashCode */
  override def equals(other: Any): Boolean =  other match {
    case that: Point3 => this.x == that.x && this.y == that.y
    case _            => false 
  }
  override def hashCode = x*41 + y // some prime number 41 

}
println("\nWith proper definition ...")

val p6  = new Point3(2,3)
val p7  = new Point3(2,3)
val p8  = new Point3(1,2)

println(p6 equals p7)     // true
println(p6 equals p8)     // false


println(p6 == p7)     // true
println(p6 == p8)     // false

val coll3 = HashSet(p6)
println(coll3 contains p7)  // true!!! HURRAY






