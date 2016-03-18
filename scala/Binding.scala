// another use of pattern for variable binding

val mytuple = (123, "abc")
val (number, string) = mytuple // binding two variables in one go
println(number)   // 123  
println(string)   // abc

// case class
abstract class Expr // slightly more efficient than using a trait here
case class Var(name: String) extends Expr
case class Number(num: Double) extends Expr
case class UnOp(operator: String, arg: Expr) extends Expr
case class BinOp(operator: String, left: Expr, right: Expr) extends Expr


val exp = new BinOp("*", Number(5), Number(1))

val BinOp(op, left, right) = exp

println(op)       // *
println(left)     // Number(5.0)
println(right)    // Number(1.0)


val increase: Int=>Int = { case x:Int => x + 5}
println(increase(12))

val second: List[Int]=>Int = {
  case x::y::_ => y
  case x::_    => throw new Exception("List should have two elements")
  case Nil     => throw new Exception("List should not be empty")
}

println(second(List(1,2,35)))

val newSecond: PartialFunction[List[Int],Int] = { // partial function
  case x::y::_ => y
}

println(newSecond(List(3,6,7)))

// checking whether a partial function is defined at a given point
println(newSecond.isDefinedAt(List(1)))   // false
println(newSecond.isDefinedAt(List(1,4))) // true


val capitals = Map("France"->"Paris", "Japan"->"Tokyo")
for((country, city) <- capitals){
  println("the capital of "+country+" is "+city)
}


val results = List(Some("apple"), None, Some("orange"))
for(Some(fruit) <-results) println(fruit) // apple orange (None does not match)

