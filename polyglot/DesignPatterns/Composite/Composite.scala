// Composite Design Pattern

// The composite design pattern consists in creating an abstract class
// or interface 'Component' which allows client code to handle certain 
// types of primitive objects of type 'Leaf' and various combinations
// thereof in a uniform way. These combinations can be of various nature
// and are unified in a common type 'Composite', where both 'Leaf' and 
// 'Composite' are subclasses of 'Component'.
//
// There are many examples where the composite pattern is applicable
// e.g. the DOM for html and abstract syntax trees for formal languages, 
// inductive data types of Haskell and Coq, etc.
//
// In the SICP course at MIT, a key idea relating to properties of
// programming languages is the existence of 'primitive objects' (Leaf)
// and 'means of combination', allowing the creation of new objects
// (Composite) while remaining within the language. The Composite 
// patterns allows us to regard every language entity as a 'Component' 
// which can be combined with other 'Component'(either 'Leaf' or 
// 'Composite') to obtain a new Component. In Lisp we could say that 
// every Component (which we shall call 'Expression') is either a Leaf 
// (which we shall call 'ExpressionLeaf') or a list of expressions 
// (which we shall call 'ExpressionComposite'). The means of combinations 
// in this case are are simply reduced to gathering objects within lists:
//
// Expression          := ExpressionLeaf | ExpressionComposite
// ExpressionComposite := Nil | Cons Expression ExpressionComposite

class Environment {
}

trait Expression {
  def eval(env: Environment) : Expression
  def apply(args: ExpressionComposite) : Expression
  def toString() : String
  def isList() : Boolean 
  def isInt() : Boolean = false
}

abstract class ExpressionLeaf extends Expression {
  override def isList() = false
}

abstract class ExpressionComposite extends Expression {
  override def isList() = true
  def isNil() : Boolean
  def foldLeft[R](init: R, operator: (R, Expression) => R) : R = {
    var out = init
    var next = this
    while(!next.isNil){
      val cell: Cons = next match {
        case x : Cons => x
        case _        => throw new ClassCastException  // isNil == false, unlikely
      }
      out = operator(out, cell.head)
      next = cell.tail
    }
    return out
  }
  def foldRight[R](init: R, operator: (Expression, R) => R) : R = {
    if(isNil) return init
    val cell : Cons = this match {
      case x : Cons => x
      case _        =>  throw new ClassCastException  // isNil == false, unlikely
    }
    // implementation not stack friendly. may need to be changed
    return operator(cell.head, cell.tail.foldRight(init, operator))
  }

  // This does not evaluate the expression, but rather returns
  // the list (itself an ExpressionComposite) of values (each 
  // value is itself an expression, albeit often of simpler type) 
  // obtained by evaluating each expression within the list
  def evalList(env: Environment) : ExpressionComposite = {
    foldRight(new Nul, (expression, list: ExpressionComposite) => 
      new Cons(expression.eval(env), list));
  }
}

class Nul extends ExpressionComposite { // Nil is a keyword in scala
  override def isNil() = true
  override def eval(env: Environment) = this  
  override def apply(list: ExpressionComposite) = 
    throw new Exception("Nil is not an operator")
  override def toString() = "Nil"
}

class Cons(car: Expression, cdr: ExpressionComposite) 
  extends ExpressionComposite {
  def head() = car
  def tail() = cdr
  override def eval(env: Environment) = {
    val vals = evalList(env)
    val values = vals match {
      case x : Cons => x
      case _        => throw new ClassCastException
    }
    val operator = values.head
    val arguments = values.tail
    operator.apply(arguments)
  }
  override def apply(args: ExpressionComposite) =
    throw new Exception("Lambda expression are not yet supported")
  override def isNil() = false
  override def toString() = foldLeft("(", (s: String, e) => s + e + " ") + "\b)"
  
} 

class ExpInt(value: Int) extends ExpressionLeaf {
  def toInt() = value
  override def eval(env: Environment) = this  // self-evaluating
  override def apply(args: ExpressionComposite) = 
    throw new Exception("An integer is not an operator")
  override def toString() = value.toString
}

abstract class Primitive extends ExpressionLeaf {
}

class Plus extends Primitive {
  override def eval(env: Environment) = this
  override def apply(args : ExpressionComposite) = {
    val sum = args.foldLeft(0, (result: Int, expression) =>
      expression match {
        case x: ExpInt => result + x.toInt
        case _         => throw new IllegalArgumentException(
          "+: argument is not a valid integer")})
    new ExpInt(sum);
  }
  override def toString() = "+"
}

class Mult extends Primitive {
  override def eval(env: Environment) = this
  override def apply(args : ExpressionComposite) = {
    val prod = args.foldLeft(1, (result: Int, expression) =>
      expression match {
        case x: ExpInt => result * x.toInt
        case _         => throw new IllegalArgumentException(
          "+: argument is not a valid integer")})
    new ExpInt(prod);
  }
 
  override def toString() = "*"
}

object Composite {
  def main(args: Array[String]){
    val env   = new Environment
    val two   = new ExpInt(2)
    val seven = new ExpInt(7)
    val five  = new ExpInt(5)
    val plus  = new Plus
    val mult  = new Mult
    val exp1  = new Cons( // (+ 2 7 5)
                    plus,
                    new Cons(
                        two,
                        new Cons(
                            seven,
                            new Cons(
                                five,
                                new Nul))))
    val exp2  = new Cons( // (* 2 (+ 2 7 5) 5)
                    mult,
                    new Cons(
                        two,
                        new Cons(
                            exp1,
                            new Cons(
                                five,
                                new Nul))))
    println("The evaluation of the Lisp expression: " + exp2);
    println("yields the value: " + exp2.eval(env))
  }
}

