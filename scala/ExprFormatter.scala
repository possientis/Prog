import Element._

 // case class
abstract class Expr // slightly more efficient than using a trait here
case class Var(name: String) extends Expr
case class Number(num: Double) extends Expr
case class UnOp(operator: String, arg: Expr) extends Expr
case class BinOp(operator: String, left: Expr, right: Expr) extends Expr


class ExprFormatter {

  protected val opGroups =
    Array(
      Set("|", "||"),
      Set("&", "&&"),
      Set("ˆ"),
      Set("==", "!="),
      Set("<", "<=", ">", ">="),
      Set("+", "-"),
      Set("*", " % ")
    )

  private val precedence = {
    val assocs =
      for {
        i <- 0 until opGroups.length
        op <- opGroups(i)
      } yield op -> i
    Map() ++ assocs
  }

  protected val unaryPrecedence = opGroups.length
  protected val fractionPrecedence = -1

  private def format(e: Expr, enclPrec: Int): Element = e match {
    case Var(name) => elem(name)
    case Number(num) => 
      def stripDot(s: String) =
        if (s endsWith ".0") s.substring(0, s.length - 2) else s
      elem(stripDot(num.toString))
    case UnOp(op, arg) =>
      elem(op) beside format(arg, unaryPrecedence)
    case BinOp("/", left, right) =>
      val top = format(left, fractionPrecedence)
      val bot = format(right, fractionPrecedence)
      val line = elem('-', top.width max bot.width, 1)
      val frac = top above line above bot
      if (enclPrec != fractionPrecedence) frac
      else elem(" ") beside frac beside elem(" ")
    case BinOp(op, left, right) =>
      val opPrec = precedence(op)
      val l = format(left, opPrec)
      val r = format(right, opPrec + 1)
      val oper = l beside elem(" "+op+" ") beside r
      if (enclPrec <= opPrec) oper
      else elem("(") beside oper beside elem(")")
  }

  // overload
  def format(e: Expr): Element = format(e, 0)

}


object ExprFormatter {
  def main(args: Array[String]){

    val f = new ExprFormatter

    val e1 = BinOp("*", BinOp("/", Number(1), Number(2)),
                        BinOp("+", Var("x"), Number(1)))
    val e2 = BinOp("+", BinOp("/", Var("x"), Number(2)),
                        BinOp("/", Number(1.5), Var("x")))
    val e3 = BinOp("/", e1, e2)

    def show(e: Expr) = println(e+": \n"+f.format(e)+" \n")

    for (val e <- Array(e1, e2, e3)) show(e)
  }
}




