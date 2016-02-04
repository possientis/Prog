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
// e.g. the DOM for html and abstract syntax trees for various 
// formal languages, inductive data types of Haskell and Coq.
//
// In the SICP course at MIT, a key idea relating to properties of
// programming languages is the existence of 'primitive objects' (Leaf)
// and 'means of combination', allowing the creation 'composite objects'
// while remaining within the language. The Composite patterns allows
// us to regard every language entity as a 'Component' which can be
// combined with other 'Components' (either 'Leaf' or 'Composite') 
// to obtain a new Component. In Lisp we could say that every Component
// (which we shall call 'Expression') is either a Leaf (which we shall
// call 'Primitive') or a list of expressions (which we shall call
// 'ExpressionList'). The means of combinations are simply reduced
// to gathering objects within lists:


abstract class Expression {
}

abstract class Primitive extends Expression {
}

abstract class ExpressionList extends Expression {
}

// this is the test class. The true 'Composite' 
// of this example is called 'ExpressionList'
public class Composite {
  public static void main(String[] args){
    System.out.println("This is running");
  }
}
