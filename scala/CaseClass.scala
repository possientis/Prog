sealed abstract class Expression
case class X() extends Expression
case class Const(value : Int) extends Expression
case class Add(left : Expression, right : Expression) extends Expression
case class Mult(left : Expression, right : Expression) extends Expression
case class Neg(expr : Expression) extends Expression



object CaseClass {
  def main(args: Array[String]){
    val expr = Add(Const(1), Mult(Const(2), Mult(X(),X()))) // 1 + 2X^2
    assert(eval(expr,3) == 19)
    val df = deriv(expr)  // 4X (if it were to be reduced)
    assert(eval(df,4) == 16)
  }

  def eval(expression : Expression, xValue : Int) : Int = expression match {
    case X() => xValue
    case Const(cst) => cst
    case Add(left, right) => eval(left, xValue) + eval(right, xValue)
    case Mult(left, right) => eval(left, xValue) * eval(right, xValue)
    case Neg(expr) => - eval(expr, xValue)
  }

  def deriv(expression : Expression) : Expression = expression match {
    case X() => Const(1)
    case Const(_) => Const(0)
    case Add(left, right) => Add(deriv(left), deriv(right))
    case Mult(left, right) => Add(Mult(deriv(left),right),Mult(left, deriv(right)))
    case Neg(expr) => Neg(deriv(expr))
  }
}
