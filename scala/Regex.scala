// from Runar Bjarnason presentation

sealed trait RegularExpression  // 'sealed' -> compiler will check exhaustiveness in pattern matching

case class LiteralExpression(
  literal: String) extends RegularExpression

case class SequenceExpression(
  expression1: RegularExpression,
  expression2: RegularExpression) extends RegularExpression

case class RepetitionExpression(
  repetition: RegularExpression) extends RegularExpression

case class AlternationExpression(
  alternative1: RegularExpression,
  alternative2: RegularExpression) extends RegularExpression



sealed trait Exp {

  def interpret(s: String): (Boolean, String) = 
    this match {
      case Lit(l) if (s startsWith l) =>  // case with a 'guard'
        (true, s drop l.length)
      case And(a,b) =>
        val (p, ns) = a interpret s
        if (p) b interpret ns else (false, s)
      case Or(a, b) =>
        val (p, ns) = a interpret s
        if (p) (true, ns) else b interpret s  // this seems wrong to me
      case Many(e)  =>
        val (p, ns) = e interpret s
        if (p) Many(e) interpret ns else (true, s)
      case _  => (false, s)
    }

  def interpret2(s: String): (Boolean, String)
}

case class Lit(l: String) extends Exp {
  def interpret2(s: String) = { 
    if(s startsWith l)
      (true, s drop l.length)
    else
      (false, s)
  }
}

case class And(a: Exp, b: Exp) extends Exp {
  def interpret2(s: String) = {
    val (p, ns) = a interpret s
    if (p)
      b interpret ns
    else
      (false, s)
  }
}

case class Or(a: Exp, b: Exp) extends Exp {
  def interpret2(s: String) = {
    val (p, ns) = a interpret s
    if (p)
      (true, ns) 
    else
      b interpret s
  }
}


case class Many(e: Exp) extends Exp {
  def interpret2(s: String) = {
    val (p, ns)  = e interpret s
    if (p)
      Many(e) interpret ns
    else
      (true, s)
    }
}
    

// 'raining&(dogs|cat)*'
val example = And(Lit("raining"),
                  Many(Or(Lit("dogs"),
                          Lit("cats"))))

println(example)  // And(Lit(raining),Many(Or(Lit(dogs),Lit(cats))))
