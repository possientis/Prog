// Composite Design Pattern
#include <iostream>
#include <string>
#include <functional>
#include <exception>
#include <assert.h>
#include <malloc.h>

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

class Expression;
class ExpressionLeaf;
class ExpressionComposite;
class Primitive;
class ExpInt;
class Plus;
class Mult;
class Cons;
class Nil;

class Environment{};

/******************************************************************************/
/*                            Expression class                                */
/******************************************************************************/

class Expression {
  public:
    virtual const Expression* eval(const Environment* env)            const = 0;
    virtual const Expression* apply(const ExpressionComposite* args)  const = 0;
    virtual std::string toString()                                    const = 0;
    virtual bool        isList()                                      const = 0;
    virtual bool        isInt() const { return false; } // ExpInt override only
    virtual ~Expression();
    const Expression* copy() const;
    static void* operator new(size_t);
    static void operator delete(void*); // always call destructor -> no good
    static void destroy(void*);         // delete when reference count is 0
  protected:
    mutable int count;                  // reference count
    Expression();
};

// base constructor simply sets reference count to 1.
Expression::Expression() : count(1){}
// base destructor does not do anything
Expression::~Expression(){}
// copy simply increases reference count
const Expression* Expression::copy() const {
  ++count;
  std::cerr << "Making copy of object " << std::hex << this << std::endl;
  return this;
}

static void* Expression::operator new(size_t size){
  void* ptr = malloc(size);
  if(ptr == nullptr){ throw new std::bad_alloc(); }
  std::cerr << "Allocating new object " << std::hex << ptr << std::endl;
  return ptr;
}

// overriding operator delete does not prevent the destructor of the object
// pointed to by the pointer argument to run. Hence it cannot be used to 
// selectively destroy objects based on a reference count.
static void Expression::operator delete(void* ptr){
  assert(ptr != nullptr);
  std::cerr << "Deallocating object " << std::hex << ptr << std::endl;
  free(ptr);
}

/******************************************************************************/
/*                          ExpressionLeaf class                              */
/******************************************************************************/

class ExpressionLeaf : public Expression {
  public:
    bool isList() const override { return false; }
    virtual ~ExpressionLeaf(){};
};

/******************************************************************************/
/*                       ExpressionComposite class                            */
/******************************************************************************/

class ExpressionComposite : public Expression {
  public:
    virtual bool isNil() const = 0;
    bool isList() const override { return true; }
    const ExpressionComposite* evalList(const Environment* env) const;
    template <typename T> 
    T* foldLeft(T* init, std::function<T*(T*,Expression*)> oper) const;
    template <typename T>
    T* foldRight(T* init, std::function<T*(Expression*,T*)> oper) const;
    virtual ~ExpressionComposite(){}
};

template <typename T>
T* ExpressionComposite::foldLeft(T* init, std::function<T*(T*,Expression*)> oper) 
const {
  return nullptr; //-------------------------------------------------------> TBI
}

template <typename T>
T* ExpressionComposite::foldRight(T* init, std::function<T*(Expression*,T*)> oper)
const {
  return nullptr; //-------------------------------------------------------> TBI
}

const ExpressionComposite* ExpressionComposite::evalList(const Environment* env) 
const {
  return nullptr; //-------------------------------------------------------> TBI
}
/******************************************************************************/
/*                                   Nil class                                */
/******************************************************************************/

class Nil : public ExpressionComposite {
  public:
    Nil(){}
    bool isNil() const override { return true; }
    const Expression* eval(const Environment* env) const override;
    const Expression* apply(const ExpressionComposite* list) const override;
    std::string toString() const override { return "Nil"; }
    ~Nil();
};

Nil::~Nil(){ std::cerr << "Nil object destroyed once\n"; }

const Expression* Nil::apply(const ExpressionComposite* list) const {
      std::cerr << "Nil is not an operator\n";
      throw new std::exception();
      return nullptr;
}

const Expression* Nil::eval(const Environment* env) const {
  return this->copy();
}


int main(){

  Nil* nil = new Nil();

  const Expression* val = nil->copy();
  std::cout << "val = " << std::hex << val << std::endl;

  delete nil;
  std::cout << "I am still alive " << std::hex << nil << std::endl;
  delete nil;
  std::cout << "I am dead at this point " << std::hex << nil << std::endl;
  /*
  Environment* env = new Environment();

  Nil* nil = new Nil();
  const Expression* val = nil->eval(env);


  delete val;
 // delete nil;
  delete env;
 */

  return 0;
}

