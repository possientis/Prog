// Composite Design Pattern
using System;
using System.Diagnostics;   // Debug.Assert

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
//

class Environment {
}

abstract class Expression {
  public abstract Expression Eval(Environment env);
  public abstract Expression Apply(ExpressionComposite args);
  public abstract override string ToString();
  public abstract bool IsList{ get; }                 // isComposite
  public virtual  bool IsInt{ get{ return false; } } // overriden by ExpInt
}

abstract class ExpressionLeaf : Expression {
  public override bool IsList{ get{ return false; } }
}

delegate R LeftOperator<R>(R r, Expression e);
delegate R RightOperator<R>(Expression e, R r);

abstract class ExpressionComposite : Expression {
  public override bool IsList{ get{ return true; } }
  public abstract bool IsNil{ get; }

  public R foldLeft<R>(R init, LeftOperator<R> oper){
    R result = init;
    ExpressionComposite next = this;
    while(!next.IsNil){
      Debug.Assert(next is Cons);
      Cons cell = (Cons) next;    // safe in view of assert
      result = oper(result, cell.Head);
      next = cell.Tail;
    }
    return result;
  }

  public R foldRight<R>(R init, RightOperator<R> oper){
    if(IsNil) return init;
    Debug.Assert(this is Cons);
    Cons cell = (Cons) this;      // safe in view of assert
    // implementation not stack friendly. may need to be changed
    return oper(cell.Head, cell.Tail.foldRight(init, oper));
  }

  // This does not Evaluate the expression, but rather returns
  // the list (itself an ExpressionComposite) of values (each 
  // value is itself an expression, albeit often of simpler type) 
  // obtained by Evaluating each expression within the list
  public ExpressionComposite EvalList(Environment env){
    // The upcast of 'new Nil()' to 'ExpressionComposite' may appear 
    // surprising, but is required to ensure the appropriate signature is 
    // inferred for the lambda expression and generic foldRight.
    return foldRight((ExpressionComposite) new Nil(), (expression, list) =>
        new Cons(expression.Eval(env), list));
  }
}

class Nil : ExpressionComposite {
  public override bool IsNil{ get{ return true; } }
  public override Expression Eval(Environment env){ return this; }  // self Eval
  public override Expression Apply(ExpressionComposite list){
    throw new InvalidOperationException("Nil is not an operator");
  }
  public override string ToString(){ return "Nil"; }
}

class Cons : ExpressionComposite {
  private readonly Expression car;          // car, head, first ...
  private readonly ExpressionComposite cdr; // cdr, tail, rest
  public Cons(Expression car, ExpressionComposite cdr){
    this.car = car;
    this.cdr = cdr;
  }
  public Expression Head { get { return car; } }
  public ExpressionComposite Tail { get { return cdr; } }
  
  public override Expression Eval(Environment env){
    ExpressionComposite vals        = EvalList(env);
    // 'this' is a Cons, hence 'vals' should be a Cons
    Debug.Assert(vals is Cons);
    Cons values = (Cons) vals;      // safe in view of assert
    Expression oper                 = values.Head;
    ExpressionComposite arguments   = values.Tail;
    return oper.Apply(arguments);
  }

  public override Expression Apply(ExpressionComposite args){
    throw new InvalidOperationException(
        "Lambda expression are not yet supported"
    );
  }

  public override bool IsNil{ get{ return false; } }
  public override string ToString(){
    return foldLeft("(", (s,e) => s + e + " ") + "\b)";
  }
}

class ExpInt : ExpressionLeaf {
  private readonly int _value;
  public ExpInt(int val){ this._value = val; }
  public int ToInt{ get{ return _value; } }
  public override Expression Eval(Environment env){ return this; } // self eval
  public override Expression Apply(ExpressionComposite args){
    throw new InvalidOperationException("An integer is not an operator");
  }
  public override string ToString(){ return _value.ToString(); }
  public override bool IsInt{ get{ return true; } }
}
  
abstract class Primitive : ExpressionLeaf {
}

class Plus : Primitive {
  public override Expression Eval(Environment env){ return this; } // self eval
  public override Expression Apply(ExpressionComposite args){
    int sum = args.foldLeft(0, (result, expression) => {
        if(expression.IsInt){
          return result + ((ExpInt) expression).ToInt;
        } else {
          throw new ArgumentException("+: argument is not a valid integer");
        }
    });
    return new ExpInt(sum);
  }
  public override string ToString(){ return "+"; }
}

class Mult : Primitive {
  public override Expression Eval(Environment env){ return this; } // self eval
  public override Expression Apply(ExpressionComposite args){
    int prod = args.foldLeft(1, (result, expression) => {
      if(expression.IsInt){
        return result * ((ExpInt) expression).ToInt;
      } else {
        throw new ArgumentException("+: argument is not a valid integer");
      }
    });
    return new ExpInt(prod);
  }
  public override string ToString(){ return "*"; }
}

public class Composite {

  public static void Main(string[] args){
    Environment env   = new Environment();
    Expression two    = new ExpInt(2);
    Expression seven  = new ExpInt(7);
    Expression five   = new ExpInt(5);
    Expression plus   = new Plus();
    Expression mult   = new Mult();
    Expression exp1   = new Cons( // (+ 2 7 5)
                            plus,
                            new Cons(
                                two,
                                new Cons(
                                    seven,
                                    new Cons(
                                        five,
                                        new Nil()))));
    Expression exp2   = new Cons( // (* 2 (+ 2 7 5) 5)
                            mult,
                            new Cons(
                                two,
                                new Cons(
                                    exp1,
                                    new Cons(
                                        five,
                                        new Nil()))));

    Console.WriteLine("The evaluation of the Lisp expression: " + exp2);
    Console.WriteLine("yields the value: " + exp2.Eval(env));
  }
}


