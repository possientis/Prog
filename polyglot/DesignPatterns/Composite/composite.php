<?php
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
//

class Environment {
}

abstract class  Expression {
  public abstract function evaluate($env);   // can't use 'eval'
  public abstract function apply($args);
  public abstract function __toString();
  public abstract function isList();
  public function isInt(){ return false; }

}

abstract class ExpressionLeaf extends Expression {
  public function isList(){ return false; }
}

abstract class ExpressionComposite extends Expression {
  public function isList(){ return true; }
  public abstract function isNil();
  public function foldLeft ($init, $operator){
    $out = $init;
    $next = $this;
    while(!$next->isNil()){
      assert($next instanceof Cons);
      $cell = $next;  // need downcast from ExpressionComposite to Cons?
      $out = $operator($out,$cell->head());
      $next = $cell->tail();
    }
    return $out;
  }
  public function foldRight($init, $operator){
    if($this->isNil()) return $init;
    assert($this instanceof Cons);
    $cell = $this;  // need downcast from ExpressionComposite to Cons?
    // implementation not stack friendly. May need to be changed.
    return $operator($cell->head(), $cell->tail()->foldRight($init, $operator));
  }
  public function evalList($env){
    return $this->foldRight(new Nil, function($exp, $list) use($env){
      return new Cons($exp->evaluate($env), $list);});
  }
}

class Nil extends ExpressionComposite {
  public function isNil(){ return true; }
  public function evaluate($env){ return $this; } // self-evaluating
  public function apply($args){
    throw new BadFunctionCallException("Nil is not an operator");}
  public function __toString(){ return "Nil"; }
}

class Cons extends ExpressionComposite {
  private $car;
  private $cdr;
  public function __construct($car, $cdr){
    $this->car = $car;
    $this->cdr = $cdr;
  }
  public function head(){ return $this->car; }
  public function tail(){ return $this->cdr; }
  public function evaluate($env){
    $values = $this->evalList($env);
    assert($values instanceof Cons);
    $operator = $values->head();
    $arguments = $values->tail();
    return $operator->apply($arguments);
  }
  public function apply($args){
    throw new BadFunctionCallException("Lambda expression are not yet supported");}
  public function isNil(){ return false; }
  public function __toString(){
    return $this->foldLeft("(", function($str,$exp){
      return $str.$exp." ";}).chr(8).")"; // don't forget 'return' !!
  }
}

class ExpInt extends ExpressionLeaf {
  private $value;
  public function __construct($value){ $this->value = $value; }
  public function toInt(){ return $this->value; }
  public function evaluate($env){ return $this; } // self-evaluating
  public function apply($args){
    throw new BadFunctionCallException("An integer is not an operator");}
  public function __toString(){ return strval($this->value); } 
  public function isInt(){ return true; }
}

abstract class Primitive extends ExpressionLeaf {
}

class Plus extends Primitive {
  public function evaluate($env){ return $this; }
  public function apply($args){
    $sum = $args->foldLeft(0, function($res, $exp){
      if($exp->isInt()){
        return $res + $exp->toInt();
      } else {
        throw new InvalidArgumentException("+: argument is not a valid integer");
      }
    });
   return new ExpInt($sum); 
  }
  public function __toString(){ return "+"; }
}

class Mult extends Primitive {
  public function evaluate($env){ return $this; }
  public function apply($args){
    $prod = $args->foldLeft(1, function($res, $exp){
      if($exp->isInt()){
        return $res * $exp->toInt();
      } else {
        throw new InvalidArgumentException("*: argument is not a valid integer");
      }
    });
   return new ExpInt($prod); 
  }
  public function __toString(){ return "*"; }
}

$env    = new Environment;
$two    = new ExpInt(2);
$seven  = new ExpInt(7);
$five   = new ExpInt(5);
$plus   = new Plus;
$mult   = new Mult;
$exp1   = new Cons( // (+ 2 7 5)
              $plus,
              new Cons(
                  $two,
                  new Cons(
                      $seven,
                      new Cons(
                          $five,
                          new Nil))));
$exp2   = new Cons( // (* 2 (+ 2 7 5) 5)
              $mult,
              new Cons(
                  $two,
                  new Cons(
                      $exp1,
                      new Cons(
                          $five,
                          new Nil))));

echo "The evaluation of the Lisp expression: ".$exp2."\n";
echo "yields the value: ". $exp2->evaluate($env)."\n";


?>
