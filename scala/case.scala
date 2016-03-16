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



// 2. All class arguments get an implicit 'val' prefix, hence become public fields. 

println(v.name)       // x
println(op.operator)  // +
println(op.left)      // Number(1.0)
println(op.right)     // Var(x)

// 3. The compiler adds natural implementation of toString, hashCode and equals.

println(op.right == Var("x")) // true
println(op.hashCode)          // 1693053929
println(op)                   // BinOp(+,Number(1.0),Var(x))

// 4. biggest advantage is pattern matching

def simplifyTop(expr: Expr): Expr = expr match {
  case UnOp("-", UnOp("-", e))  => e // Double negation
  case BinOp("+", e, Number(0)) => e // Adding zero
  case BinOp("*", e, Number(1)) => e // Multiplying by one
  case _ => expr 
}

println(simplifyTop(UnOp("-", UnOp("-", Var("x")))))  // Var(x)

// the match expression:
//   selector match { alternatives }
// rather than: 
//   switch (selector) { alternatives }

// always cover all cases, even if there is nothing to do
def test(expr: Expr): Unit = expr match {
  case BinOp(op, left, right) => println(expr+"is a binary operation")
  case _ => // nothing to do, needed, otherwise will throw MatchError
}


// examples of constant patterns
def describe(x: Any) = x match {
  case 5 => "five"                // constant literal
  case true => "truth"            // constant literal
  case "hello" => "hi!"           // constant literal
  case Nil => "the empty list"    // variable name, but upper case 'N'
  case _ => "something else"
}

// variable pattern matches any object
val x0 = 10 match {
  case 0 => "zero"
  case somethingElse => "not zero: " + somethingElse // will always match
}

// the importance of lower versus upper case first letter

// import Math._  // deprecated
import scala.math

// however, never mind deprecation, we are trying to make a point
println(scala.math.E match {
  case scala.math.Pi => "strange math? Pi = "+ scala.math.Pi
  case e  => "nothing strange: "+e
})


import Math._  // deprecated, but needed here to illustrae the point

println(E match {
  case Pi => "strange math? Pi = "+Pi
  case e  => "nothing strange: " + e
})

val pi = 3.14159

println(E match {
  case pi => "strange math? Pi = "+pi // pi is variable pattern, not constant
})







