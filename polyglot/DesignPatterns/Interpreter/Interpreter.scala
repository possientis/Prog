// Interpreter Design Pattern

// from the Gang of Four book:
// "If a particular kind of problem occurs often enough, then it might be
// worthwhile to express instances of the problem as sentences in a simple
// language. Then you can build an interpreter that solves the problem by 
// interpreting these sentences. For example, searching for strings that 
// match a pattern is a common problem. Regular expressions are a standard 
// language for specifying patterns of strings. Rather than building custom 
// algorithms to match each pattern against strings, search algorithms could 
// interpret a regular expression that specifies a set of strings to match."

// Each regular expression r has an associated language L(r) (which is a set
// of strings) defined by the recursion:
//
//  - r = Lit(s)        -> L(r) = {s}
//  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
//  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
//  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
//
//  where given A,B sets of strings the product A.B is defined as the set of 
//  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
//  A^0 = {""} and A^1 = A. 
//
// Given a regular expression r and a string s, many reasonable questions 
// can be asked in relation to r and s. When using the command 'grep', the
// question being asked is whether there exist a substring s' of s which
// belongs to the language of r. One of the first questions of interest is
// of course whether s itself belongs to L(r).

// This is scala: we use pattern matching rather than overrides
sealed trait Exp {
  
  override def toString : String =
    this match {
      case Lit(literal)     => literal
      case And(left, right) => "" + left + right
      case Or(left, right)  => "(" + left + "|" + right + ")"
      case Many(regex)      => "(" + regex + ")*"
    }    

  def interpret(input : String) : List[String] = 
    this match {
      case Lit(literal)     =>
        if (input startsWith literal){ // literal is a prefix of input
          List(literal)
        } else {
          Nil
        }
      case And(left, right) =>  
        var result : List[String] = Nil
        for(s1 <- left.interpret(input)){
          val remainder = input.substring(s1.length)
          for(s2 <- right.interpret(remainder)){
            result = (s1 + s2)::result
          }
        }
        result
      case Or(left, right)  => 
        left.interpret(input) ::: right.interpret(input)
      case Many(regex)      => 
        var result = List("")
        for(s1 <- regex.interpret(input)){
          if(!s1.isEmpty){
            val remainder = input.substring(s1.length)
            for(s2 <- this.interpret(remainder)){  // recursive call
              result = (s1 + s2)::result
            }
          }
        }
        result
    }
  def recognize(input: String): Boolean = interpret(input).contains(input)
}

case class Lit(literal: String) extends Exp {}
case class And(left: Exp, right: Exp) extends Exp {}
case class Or(left: Exp, right: Exp) extends Exp {}
case class Many(regex: Exp) extends Exp {}




object Interpreter {
  def main(args: Array[String]){
    val a = Lit("a")
    val b = Lit("b")
    val c = Lit("c")
    
    val aa = And(a, Many(a))  // one or mare 'a'
    val bb = And(b, Many(b))  // one or mare 'b'
    val cc = And(c, Many(c))  // one or mare 'c'

    val regex = Many(And(Or(aa,bb),cc))
    val string = "acbbccaaacccbbbbaaaaaccccc"

    println("regex = " + regex);
    println("string = \"" + string + "\"");
    println("The recognized prefixes are:");
    
    var result : List[String] = Nil
    for(i <- 0 to string.length){
      val test = string.substring(0,i)
      if(regex.recognize(test)){
        result = ("\"" + test + "\"")::result
      }
    }
    println(result.reverse.mkString("[",", ","]"))
  }
}
