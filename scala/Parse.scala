import scala.util.parsing.combinator.syntactical._

class Arith extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "+", "-", "*", "/")

  def expr: Parser[Any] =
    term ∼ rep("+" ∼ term | "-" ∼ term)
  def term: Parser[Any] =
    factor ∼ rep("*" ∼ factor | "/" ∼ factor)
  def factor: Parser[Any] =
    "(" ∼ expr ∼ ")" | numericLit
}



object Parse extends Arith {
  def main(args: Array[String]) {
    val tokens = new lexical.Scanner(args(0))
    println("input: "+args(0))
    println(phrase(expr)(tokens))
  }
}



