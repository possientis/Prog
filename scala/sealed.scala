// case class
// using the sealed keyword gives better compile support for pattern match
// because we know no know all subclasses are in the file
sealed abstract class Expr // slightly more efficient than using a trait here
case class Var(name: String) extends Expr
case class Number(num: Double) extends Expr
case class UnOp(operator: String, arg: Expr) extends Expr
case class BinOp(operator: String, left: Expr, right: Expr) extends Expr


// The 'case' class modifier makes the compiler add syntactic sugar:

// 1. factory function, Var("x") instead of new Var("x")
val v = Var("x")
val op = BinOp("+", Number(1),v)


// cases are missing, because root class is sealed, you get compiler warning
// you can make warning go away with a third 'catch all' case
// or you can add the @unchecked annotation (decorator)
def describe(e: Expr): String = (e: @unchecked) match {
  case Number(x)  => "a number"
  case Var(_)     => "a variable"
//  case _          => throw new RuntimeException
}

