// Composite Design Pattern
import java.util.*;
import java.util.function.*;

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

abstract class Expression {
  public abstract  Expression eval(Environment env);
  public abstract  Expression apply(ExpressionComposite args);
  public abstract  String toString();
  public abstract  boolean isList();         // isComposite
  public boolean   isInt(){ return false ;} // overriden by ExpInt 
}

abstract class ExpressionLeaf extends Expression {
  @Override
  public boolean isList(){ return false;}
}

abstract class ExpressionComposite extends Expression {
  @Override
  public boolean isList(){ return true; }
  public abstract boolean isNil();
  public <R> R foldLeft(R init, BiFunction<R,Expression,R> operator){
    R out = init;
    ExpressionComposite next = this;
    while(!next.isNil()){
      assert(!next.isNil());
      Cons cell = (Cons) next;  // safe in view of assert
      out = operator.apply(out, cell.head());
      next = cell.tail();
    }
    return out;
  }
  public <R> R foldRight(R init, BiFunction<Expression,R,R> operator){
    if(isNil()) return init;
    assert(!isNil());
    Cons cell = (Cons) this;  // safe in view of assert
    // implemantation not stack friendly. May need to be changed
    return operator.apply(cell.head(), cell.tail().foldRight(init,operator));
  } 
  // This does not evaluate the expression, but rather returns
  // the list (itself an ExpressionComposite) of values (each 
  // value is itself an expression, albeit often of simpler type) 
  // obtained by evaluating each expression within the list
  public ExpressionComposite evalList(Environment env){
    return foldRight((ExpressionComposite) new Nil(), (expression, list) ->
        new Cons(expression.eval(env), list));
  }
}

class Nil extends ExpressionComposite {
  public Nil(){}
  @Override
  public boolean isNil(){ return true; }
  @Override
  public Expression eval(Environment env){ return this; } //self evaluating
  @Override
  public Expression apply(ExpressionComposite list){
    throw new UnsupportedOperationException("Nil is not an operator");
  }
  @Override
  public String toString(){ return "Nil"; }
}

class Cons extends ExpressionComposite {
  private Expression car;
  private ExpressionComposite cdr;

  public Cons(Expression car, ExpressionComposite cdr){
    this.car = car; 
    this.cdr = cdr;
  }

  public Expression head(){ return car;}
  public ExpressionComposite tail(){ return cdr; }

  @Override
  public boolean isNil(){ return false; }
  @Override
  public String toString(){
    return foldLeft("(", (s,e) -> s + e.toString() + " ") + ")";
  }
  @Override
  public Expression apply(ExpressionComposite args){
    throw new UnsupportedOperationException(
      "Lambda expression are not yet supported"
    );
  }
  @Override
  public Expression eval(Environment env){
    ExpressionComposite vals      = evalList(env);
    // 'this' is a Cons, 'values' should be a Cons
    assert(!vals.isNil());        
    Cons values = (Cons) vals;    // safe in view of assert
    Expression operator           = values.head();
    ExpressionComposite arguments = values.tail();
    return operator.apply(arguments);
  }
}

class ExpInt extends ExpressionLeaf {
  private final int value;
  public ExpInt(Integer value){ this.value = value; }
  public Integer toInt(){ return value; }

  @Override
  public Expression eval(Environment env) { return this ;}  // self-evaluating
  @Override
  public String toString(){ return String.valueOf(value);}
  @Override
  public boolean isInt(){ return true; }
  @Override
  public Expression apply(ExpressionComposite args){
    throw new UnsupportedOperationException("An integer is not an operator");
  }
}

abstract class Primitive extends ExpressionLeaf {
}

class Plus extends Primitive {
  @Override
  public String toString(){ return "+"; }
  @Override
  public Expression eval(Environment env){ return this; }
  @Override
  public Expression apply(ExpressionComposite args){
    return args.foldLeft(new ExpInt(0), (result, expression) -> {
      if(expression.isInt()){
        return new ExpInt((result.toInt()) + ((ExpInt) expression).toInt());
      }
      else{
        throw new IllegalArgumentException(
          "+: argument is not a valid integer"
        );
      }
    });
  }
}

class Mult extends Primitive {
  @Override
  public String toString(){ return "*"; }
  @Override
  public Expression eval(Environment env){ return this; }
  @Override
  public Expression apply(ExpressionComposite args){
    return args.foldLeft(new ExpInt(1), (result, expression) -> {
      if(expression.isInt()){
        return new ExpInt((result.toInt()) * ((ExpInt) expression).toInt());
      }
      else{
        throw new IllegalArgumentException(
          "*: argument is not a valid integer"
        );
      }
    });
  }
}

class Environment {
}

// test class
public class Composite {
  public static void main(String[] args){
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
    System.out.println("The evaluation of Lisp expression: " + exp2);
    System.out.println("yields the value: " + exp2.eval(env));
  }
}
