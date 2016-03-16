// case class
abstract class Expr // slightly more efficient than using a trait here
case class Var(name: String) extends Expr
case class Number(num: Double) extends Expr
case class UnOp(operator: String, arg: Expr) extends Expr
case class BinOp(operator: String, left: Expr, right: Expr) extends Expr


// The 'case' class modifier makes the compiler add syntactic sugar:

// 1. factory function, Var("x") instead of new Var("x")
val v = Var("x")
val op = BinOp("+", Number(1),v)

def simplifyAdd(e: Expr) = e match { // pattern matching with guard
  case BinOp("+",x,y) if x == y => BinOp("*", x, Number(2)) // with guard
  case _                        => e
}

val e = BinOp("+",Number(5),Number(5))
println(simplifyAdd(e))



