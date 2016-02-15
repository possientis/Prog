// Composite Design Pattern
#include <iostream>
#include <string>
#include <functional>
#include <exception>

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
class Environment;
class Expression;
class ExpressionComposite;

class Expression {
  protected:
    mutable int count;  // reference counter
  public:
    Expression(){ count = 1; }
    virtual ~Expression(){};
    virtual const Expression* clone() const = 0;
    virtual const Expression* eval(const Environment* env) const = 0;
    virtual const Expression* apply(const ExpressionComposite* args) const = 0;
    virtual std::string toString() const = 0;
    virtual bool isList() const = 0;              // meaning 'isComposite'
    virtual bool isInt() const { return false; }  // overriden in class ExpInt only
};

class ExpressionLeaf : public Expression {
  public:
    virtual ~ExpressionLeaf(){};
    bool isList() const override { return false; }
};


class ExpressionComposite : public Expression {
  public:
    virtual ~ExpressionComposite(){}
    virtual bool isNil() const = 0;
    bool isList() const override { return true; }
    // foldLeft
    template <typename T> 
    T* foldLeft(T* init, std::function<T*(T*,Expression*)> oper) const;
    // foldRight
    template <typename T>
    T* foldRight(T* init, std::function<T*(Expression*,T*)> oper) const;
    // evalList
    const ExpressionComposite* evalList(Environment* env) const;
};

class Nil : public ExpressionComposite {
  public:
    ~Nil(){}
    bool isNil() const override { return true; }
    const Nil* clone() const override { ++count; return this; } 
    const Expression* eval(const Environment* env) const override {
      return this->clone();
    }
    const Expression* apply(const ExpressionComposite* list) const override {
      std::cerr << "Nil is not an operator\n";
      throw new std::exception();
    }
    std::string toString() const override { return "Nil"; }
};



template <typename T>
T* ExpressionComposite::foldLeft(T* init, std::function<T*(T*,Expression*)> oper) 
const {
  return nullptr; //---------------------------------------------------------> TBI
}

template <typename T>
T* ExpressionComposite::foldRight(T* init, std::function<T*(Expression*,T*)> oper)
const {
  return nullptr; //---------------------------------------------------------> TBI
}

const ExpressionComposite* ExpressionComposite::evalList(Environment* env) const {
  return nullptr; //---------------------------------------------------------> TBI
}

class Environment {
};

int main(){

  const Environment* env = new Environment();
  const Expression* nil = new Nil();
  const Expression* val = nil->eval(env);
  
  std::cout << "nil = " << nil->toString() << ", eval = " << val->toString();

  delete nil;
  delete env;

  return 0;
}

