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

function Environment(){
}

// there is no assert in Javascript
function assert(condition) {
  if (!condition) {
    "Assertion failed";
  }
}

/******************************************************************************/
/*                            class Expression                                */
/******************************************************************************/

function Expression(){}

Expression.prototype.eval = function(env){
  throw "Expression::eval is not implemented";}
Expression.prototype.apply = function(args){
  throw "Expression::apply is not implemented";}
Expression.prototype.toString2 = function(){
  throw "Expression::toString2 is not implemented";}
Expression.prototype.isList = function(){
  throw "Expression::isList is not implemented";}
Expression.prototype.isInt = function(){
  return false;  // overriden by class ExpInt
}

/******************************************************************************/
/*                          class ExpressionLeaf                              */
/******************************************************************************/

function ExpressionLeaf(){ Expression.call(this); }
ExpressionLeaf.prototype        = Object.create(Expression.prototype);
ExpressionLeaf.prototype.isList = function(){ return false; }

/******************************************************************************/
/*                         class ExpressionComposite                          */
/******************************************************************************/

function ExpressionComposite(){ Expression.call(this); }
ExpressionComposite.prototype           = Object.create(Expression.prototype);
ExpressionComposite.prototype.isNil     = function(){
  throw "ExpressionComposite::isNil is not implemented";}
ExpressionComposite.prototype.isList    = function(){ return true; }
ExpressionComposite.prototype.foldLeft  = function(init, operator){
  var out = init;
  var next = this;
  while(!next.isNil()){
    assert(next instanceof Cons);
    var cell = next;            // would be downcasting in other languages
    out = operator(out, cell.head());
    next = cell.tail();
  }
  return out;
}
ExpressionComposite.prototype.foldRight = function(init, operator){
  if(this.isNil()) return init;
  assert(this instanceof Cons);
  var cell = this;              // would be downcasting in other languages
  // implementation not stack friendly. may need to be changed.
  return operator(cell.head(), cell.tail().foldRight(init,operator));
}
// This does not evaluate the expression, but rather returns
// the list (itself an ExpressionComposite) of values (each 
// value is itself an expression, albeit often of simpler type) 
// obtained by evaluating each expression within the list
ExpressionComposite.prototype.evalList = function(env){
  return this.foldRight(new Nil, function(exp,list){
    return new Cons(exp.eval(env), list);
  });
}

/******************************************************************************/
/*                                  class Nil                                 */
/******************************************************************************/
function Nil(){ ExpressionComposite.call(this); }
Nil.prototype           = Object.create(ExpressionComposite.prototype);
Nil.prototype.isNil     = function(){ return true; }
Nil.prototype.eval      = function(env){ return this; }  // self-evaluating
Nil.prototype.apply     = function(list){ throw "Nil is not an operator"; }
Nil.prototype.toString2  = function(){ return "Nil"; }

/******************************************************************************/
/*                                  class Cons                                */
/******************************************************************************/
function Cons(car, cdr){
  ExpressionComposite.call(this);
  this.car = car;   // car, head, first
  this.cdr = cdr;   // cdr, tail, rest
}
Cons.prototype = Object.create(ExpressionComposite.prototype);
Cons.prototype.head = function(){ return this.car; }
Cons.prototype.tail = function(){ return this.cdr; }
Cons.prototype.eval = function(env){
  var values = this.evalList(env);
  assert(values instanceof Cons);
  var operator = values.head();
  var argList  = values.tail();
  return operator.apply(argList);
}
Cons.prototype.apply = function(args){
  throw "Lambda expression are not yet supported";}
Cons.prototype.isNil = function(){ return false; }
Cons.prototype.toString2 = function(){
  return this.foldLeft("(", function(str, exp){
    return str + exp.toString2() + " ";}) + "\b)";
}
     
/******************************************************************************/
/*                                class ExpInt                                */
/******************************************************************************/

function ExpInt(value){
  ExpressionLeaf.call(this);
  this.value = value;
}
ExpInt.prototype          = Object.create(ExpressionLeaf.prototype)
ExpInt.prototype.toInt    = function(){ return this.value; }
ExpInt.prototype.eval     = function(env){ return this; } // self-evaluating
ExpInt.prototype.apply    = function(args){throw "An integer is not an operator";}
ExpInt.prototype.toString2 = function(){ return this.value.toString(); }
ExpInt.prototype.isInt    = function(){ return true; }


/******************************************************************************/
/*                                class Primitive                             */
/******************************************************************************/
function Primitive(){ ExpressionLeaf.call(this); }
Primitive.prototype = Object.create(ExpressionLeaf.prototype)


/******************************************************************************/
/*                                class Plus                                  */
/******************************************************************************/
function Plus(){ Primitive.call(this); }
Plus.prototype        = Object.create(Primitive.prototype);
Plus.prototype.eval   = function(env){ return this; }
Plus.prototype.apply  = function(args){
  var sum = args.foldLeft(0, function(res, exp){
    if(exp.isInt()){
      return res + exp.toInt();
    } else {
      throw "+: argument is not a valid integer";
    }
  });
  return new ExpInt(sum);
}
Plus.prototype.toString2 = function(){ return "+"; }

/******************************************************************************/
/*                                class Mult                                  */
/******************************************************************************/

function Mult(){ Primitive.call(this); }
Mult.prototype        = Object.create(Primitive.prototype);
Mult.prototype.eval   = function(env){ return this; }
Mult.prototype.apply  = function(args){
  var prod = args.foldLeft(1, function(res, exp){
    if(exp.isInt()){
      return res * exp.toInt();
    } else {
      throw "*: argument is not a valid integer";
    }
  });
  return new ExpInt(prod);
}
Mult.prototype.toString2 = function(){ return "*"; }


/******************************************************************************/
/*                                    Main                                    */
/******************************************************************************/
  var env   = new Environment;

  var two   = new ExpInt(2);
  var seven = new ExpInt(7);
  var five  = new ExpInt(5);
  var plus  = new Plus();
  var mult  = new Mult();
  var exp1  = new Cons( // (+2 7 5)
              plus,
              new Cons(
                  two,
                  new Cons(
                      seven,
                      new Cons(
                          five,
                          new Nil))));
  var exp2  = new Cons( // (* 2 (+ 2 7 5) 5)
              mult,
              new Cons(
                  two,
                  new Cons(
                      exp1,
                      new Cons(
                          five,
                          new Nil))));

print("The evaluation of the Lisp expression: " + exp2.toString2());
print("yields the value: " + exp2.eval(env).toString2());


