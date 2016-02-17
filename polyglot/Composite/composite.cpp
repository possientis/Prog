// Composite Design Pattern
#include <iostream>
#include <string>
#include <functional>
#include <exception>
#include <assert.h>

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

// used for primitive reporting of memory allocations and deallocations
void memory_log(std::string message, const void* ptr){
  std::cerr << message << std::hex << ptr << std::endl;
}

class Environment{};
class Expression;
class ExpressionComposite;

class ExpressionData {
  friend Expression;
  mutable int count;  // reference count
};

class Expression {
  public:
    virtual ~Expression();
    virtual const Expression& eval(Environment env)                   const = 0;
    virtual const Expression& apply(const ExpressionComposite& args)  const = 0;
    virtual std::string toString()                                    const = 0;
    virtual bool        isList()                                      const = 0;
    virtual bool        isInt() const { return false; }
  protected:
    Expression(ExpressionData* impl);   // derived class passing concrete pointer
    const Expression& clone() const;
  private:
    const ExpressionData* const _impl;  // unique data member
};


Expression::Expression(ExpressionData* impl) : _impl(impl){
  assert(_impl != nullptr); 
  _impl->count = 1; 
  memory_log("allocating new object ", _impl);
}

Expression::~Expression(){
  assert(_impl != nullptr);
  _impl->count--; 
  if(_impl->count == 0){
    memory_log("deallocating object ", _impl);
    delete _impl; 
  } 
  else{
    memory_log("deleting copy of object ", _impl);
  }
}

const Expression& Expression::clone() const {
  memory_log("making copy of object ", _impl);
  _impl->count++;
  return (*this);
}

class ExpressionLeaf : public Expression {
  public:
    virtual ~ExpressionLeaf(){};
    bool isList() const override { return false; }
  protected:
    ExpressionLeaf(ExpressionData* impl): Expression(impl){}
};

class ExpressionComposite : public Expression {
  public:
    virtual ~ExpressionComposite(){}
    virtual bool isNil() const = 0;
    bool isList() const override { return true; }
    ExpressionComposite& evalList(Environment env) const;
    template <typename T> 
    T& foldLeft(T& init, std::function<T&(T&,Expression&)> oper) const;
    template <typename T>
    T& foldRight(T& init, std::function<T&(Expression&,T&)> oper) const;
  protected:
    ExpressionComposite(ExpressionData* impl): Expression(impl){}
};

class Nil : public ExpressionComposite {
  public:
    ~Nil(){}
    Nil();
    bool isNil() const override { return true; }
    const Expression& eval(Environment env) const override;
    const Expression& apply(const ExpressionComposite& list) const override;
    std::string toString() const override { return "Nil"; }
};

Nil::Nil() : ExpressionComposite(new ExpressionData()){}

const Expression& Nil::apply(const ExpressionComposite& list) const {
      std::cerr << "Nil is not an operator\n";
      throw new std::exception();
}

const Expression& Nil::eval(Environment env) const {
  return this->clone();
}

template <typename T>
T& ExpressionComposite::foldLeft(T& init, std::function<T&(T&,Expression&)> oper) 
const {
  //return nullptr; //-------------------------------------------------------> TBI
}

template <typename T>
T& ExpressionComposite::foldRight(T& init, std::function<T&(Expression&,T&)> oper)
const {
  //return nullptr; //-------------------------------------------------------> TBI
}

ExpressionComposite& ExpressionComposite::evalList(Environment env) const {
  //return nullptr; //-------------------------------------------------------> TBI
}


int main(){

  Environment env;

  Nil nil;
  const Expression& val = nil.eval(env);
  std::cout << "nil = " << nil.toString() << std::endl;
  std::cout << "val = " << val.toString() << std::endl;

  val.~Expression();

  return 0;
}

