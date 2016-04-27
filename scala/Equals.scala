// == is declared final in class Any. Cannot be overriden
// simply override 'equals' if you need to change the 
// meaning of ==
// final def ==(other: Any) : Boolean = this.equals(other)


// common pitfalls that may cause inconsistent behavior of equals

// 1. Defining equals with the wrong signature
// 2. Changing equals without also changing hashCode
// 3. Defining equals in terms of mutable fields
// 4. Failing to define equals as an equivalence relation

class Point(val x: Int, val y:Int){

  /** an utterly wrong definition of Equals **/
  // this is not even an override, so doesnt affect ==
  // try to add 'override' qualifier and it will not compile
  def equals(other: Point): Boolean =
    this.x == other.x && this.y == other.y

}


val p1 = new Point(2,3)
val p2 = new Point(2,3)
val q  = new Point(1,2)

println(p1 equals p2)   // true
println(p1 equals q)    // false


println(p1 == p2)   // false !!!!!!!!! (equals not an override)
println(p1 == q)    // false


