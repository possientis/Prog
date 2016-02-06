// Composite Design Pattern
import java.util.*;

// The composite design pattern consists in creating an abstract class
// or interface 'Component' which allows client code to handle certain 
// types of primitive objects of type 'Leaf' and various combinations
// thereof in a uniform way. These combinations can be of various nature
// and are unified in a common type 'Composite', where both 'Leaf' and 
// 'Composite' are subclasses of 'Component'.
//
// There are many examples where the composite pattern is applicable
// e.g. the DOM for html and abstract syntax trees for formal languages, 
// inductive data types of Haskell and Coq.
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
  public boolean   isList(){ return false; }  // overriden by Composite only
  public boolean   isInt() { return false; }  // overriden by Int only    
  public abstract  Expression eval(Environment env);
  public abstract  String toString();

}

abstract class ExpressionLeaf extends Expression {
}

abstract class ExpressionComposite extends Expression {
  @Override
  public boolean isList(){ return true; }
  public boolean isNil(){ return false; }   // overriden by Nil only
  public abstract Expression getCar() throws Exception;
  public abstract ExpressionComposite getCdr() throws Exception; 

}

class Nil extends ExpressionComposite {
  @Override
  public boolean isNil(){ return true; }
  @Override
  public Expression eval(Environment env){ return this; } //self evaluating
  @Override
  public String toString(){ return "Nil"; }
  @Override
  public Expression getCar() throws Exception { 
    throw new Exception("Nil has no car"); 
  }
  @Override
  public ExpressionComposite getCdr() throws Exception { 
    throw new Exception("Nil has no cdr"); 
  }
}

class Cons extends ExpressionComposite {
  private Expression car;
  private ExpressionComposite cdr;

  public Cons(Expression car, ExpressionComposite cdr){
    this.car = car; this.cdr = cdr;
  }
  @Override
  public Expression getCar(){ return car;}
  @Override
  public ExpressionComposite getCdr(){ return cdr; }
  @Override
  public String toString(){
    String out = "(" + car.toString();
    ExpressionComposite next = cdr;
    while(!next.isNil()){
      try{
        out += " " + next.getCar().toString();
        next = next.getCdr();
      }
      catch(Exception e){
        System.out.println("Unexpected exception occurred");
      }
    }
    out += ")";
    return out;
  }
  @Override
  public Expression eval(Environment env){ return null; } // TBI
}



class ExpInt extends ExpressionLeaf {
  private final int value;
  @Override
  public boolean isInt(){ return true; }
  public ExpInt(int value){ this.value = value; }
  public Expression eval(Environment env) { return this ;}  // self-evaluating
  public String toString(){ return String.valueOf(value);}
}

abstract class ExpOperation extends ExpressionLeaf {

}

abstract class BinaryOp extends ExpOperation {
}

class Plus extends BinaryOp {
  public String toString(){ return "+"; }
  public Expression eval(Environment env){ return this; }
}


class Environment {
}

// test class
public class Composite {
  public static void main(String[] args){
    Expression exp1 = new ExpInt(11);
    Expression exp2 = new ExpInt(23);
    Expression exp3 = new Plus();
    Expression exp4 = new Cons(exp3, new Cons (exp1, new Cons(exp2, new Nil())));
    System.out.println(exp4);

  }
}
