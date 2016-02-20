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
    static void destroy(const Expression*);  // to be used rather than 'delete'
    static void memory_log(std::string message, const void* address);
  protected:
    mutable int count;                  // reference count
    Expression();
};

void Expression::memory_log(std::string message, const void* address){
  // comment out line to disable messaging
  std::cerr << message << " " << std::hex << address << std::endl;
}
// base constructor simply sets reference count to 1.
Expression::Expression() : count(1){
  memory_log("New object created",this);
}
// base destructor does not do anything
Expression::~Expression(){
  memory_log("Destroying existing object", this);
}
// copy simply increases reference count
const Expression* Expression::copy() const {
  ++count;
  memory_log("Making copy of object", this);
  return this;
}

// this is not virtual ...
void Expression::destroy(const Expression* exp){
  assert(exp != nullptr);
  assert(exp->count > 0);
  exp->count--;
  if(exp->count == 0){
    delete exp; // .. but this will call virtual destructor
  }
  else{
    memory_log("Deleting copy of object",exp);
  }
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
    T* foldLeft(T* init, std::function<T*(T*,const Expression*)> oper) const;
    template <typename T>
    T* foldRight(T* init, std::function<T*(const Expression*,T*)> oper) const;
    virtual ~ExpressionComposite(){}
};



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
    ~Nil(){};
};


const Expression* Nil::apply(const ExpressionComposite* list) const {
      std::cerr << "Nil is not an operator\n";
      throw new std::exception();
      return nullptr;
}

const Expression* Nil::eval(const Environment* env) const {
  return this->copy();
}

/******************************************************************************/
/*                                   Cons class                               */
/******************************************************************************/

class Cons : public ExpressionComposite {
  private:
    const Expression* car;          // car, first, head ...
    const ExpressionComposite* cdr; // cdr, rest, tail ...
  public:
    ~Cons();
    Cons(const Expression* car, const ExpressionComposite* cdr);
    const Expression* eval(const Environment*) const override;
    const Expression* apply(const ExpressionComposite*) const override;
    std::string toString() const override;
    bool isNil() const override { return false; }
    const Expression* head() const;           // caller needs to deallocate
    const ExpressionComposite* tail() const;  // caller needs to deallocate
};

Cons::~Cons(){
  destroy(car); // not calling delete, taking into account ref count
  destroy(cdr); // not calling delete, taking into account ref count
}

Cons::Cons(const Expression* car, const ExpressionComposite* cdr){
  assert(car != nullptr);
  assert(cdr != nullptr);
  this->car = car;  // not using copy, Cons object takes ownership of pointers
  this->cdr = cdr;  // so caller need not deallocate car and cdr, but only
                    // focus on deallocating Cons object.
}

const Expression* Cons::eval(const Environment* env) const {
  std::cerr << "Cons::eval is not yet implemented\n"; //-------------------> TBI
  throw new std::exception();
}

const Expression* Cons::apply(const ExpressionComposite* args) const {
  std::cerr << "Lambda expression are not yet supported\n";
  throw new std::bad_function_call();
}

const Expression* Cons::head() const { 
  return car->copy();   // copy, hence caller should deallocate
}

const ExpressionComposite* Cons::tail() const {
  return static_cast<const ExpressionComposite*>(cdr->copy());  // copy, idem
}

std::string Cons::toString() const {
  return "Cons::toString() is not yet implemented"; //---------------------> TBI
}

/******************************************************************************/
/*                             foldLeft/foldRight                             */
/******************************************************************************/

template <typename T> T* ExpressionComposite::foldLeft(
    T* init, 
    std::function<T*(T*,const Expression*)> oper
) const {
  assert(init != nullptr);
  T* out = init;
  const ExpressionComposite* next = this->copy(); // deallocated further down
  while(!next->isNil()){
    assert(!next->isNil());
    const Cons* cell = static_cast<const Cons*>(next);  // safe in view of assert
    const Expression* head = cell->head();
    out = oper(out,head);
    Expression::destroy(head);  // deallocation of copy 
    next = cell->tail();
    Expression::destroy(cell);  // deallocation of cell (previous next)
  }
  Expression::destroy(next);
  return out;
}

template <typename T> T* ExpressionComposite::foldRight(
    T* init, 
    std::function<T*(const Expression*,T*)> oper
) const {
  assert(init != nullptr);
  if(isNil()) return init;
  assert(!isNil());
  const Cons* cell = static_cast<const Cons*>(this);  // safe in view of assert
  const Expression* head = cell->head();              // returns a copy
  const ExpressionComposite* tail = cell->tail();    // also a copy
  // recursive call
  T* result = tail->foldRight(init,oper);
  result = oper(head,result);
  Expression::destroy(head);
  Expression::destroy(tail);
  return result;
}


/******************************************************************************/
/*                                  ExpInt class                              */
/******************************************************************************/

class ExpInt : public ExpressionLeaf {
  private:
    const int _value;
  public:
    ~ExpInt(){}
    const Expression* eval(const Environment*) const override;
    const Expression* apply(const ExpressionComposite*) const override;
    std::string toString() const override;
    bool isInt() const override { return true; }
    ExpInt(int value) : _value(value){}
    int toInt() const { return _value; }
};

const Expression* ExpInt::eval(const Environment* env) const {
  assert(env != nullptr);
  return this->copy();
}

const Expression* ExpInt::apply(const ExpressionComposite* args) const {
  std::cerr << "An integer is not an operator\n";
  throw new std::bad_function_call();
}

std::string ExpInt::toString() const {
  return std::to_string(_value);
}

/******************************************************************************/
/*                               Primitive class                              */
/******************************************************************************/

class Primitive : public ExpressionLeaf {
  public:
    ~Primitive(){}
};


/******************************************************************************/
/*                                 Plus class                                 */
/******************************************************************************/

class Plus : public Primitive {
  public:
    ~Plus(){}
    Plus(){}
    const Expression* eval(const Environment*) const override;
    const Expression* apply(const ExpressionComposite*) const override;
    std::string toString() const override { return "+"; }
};

const Expression* Plus::eval(const Environment* env) const {
  assert(env != nullptr);
  return this->copy();
}

const Expression* Plus::apply(const ExpressionComposite* args) const{
  std::cerr << "Plus::apply is not yet implemented\n"; // ---------------> TBI
  throw new std::exception();
}

/******************************************************************************/
/*                                 Mult class                                 */
/******************************************************************************/

class Mult : public Primitive {
  public:
    ~Mult(){}
    Mult(){}
    const Expression* eval(const Environment*) const override;
    const Expression* apply(const ExpressionComposite*) const override;
    std::string toString() const override { return "*"; }
};

const Expression* Mult::eval(const Environment* env) const {
  assert(env != nullptr);
  return this->copy();
}

const Expression* Mult::apply(const ExpressionComposite* args) const{
  std::cerr << "Mult::apply is not yet implemented\n"; // ---------------> TBI
  throw new std::exception();
}

/******************************************************************************/
/*                                   Testing                                  */
/******************************************************************************/

void Nil_test(){
  Environment* env = new Environment();
  const Expression* nil = new Nil();

  // eval
  const Expression* val = nil->eval(env);
  if(val != nil){
    std::cerr << "Nil_test: unit test 1.0 failing\n";
    throw new std::exception();
  }
  // apply
  try{
    nil->apply(static_cast<const ExpressionComposite*>(nil));
    std::cerr << "Nil_test: unit test 1.1 failing\n";
  } catch(std::exception* e){
    // as expected
  }
  // toString
  if(nil->toString() != "Nil"){
    std::cerr << "Nil_test: unit test 2.0 failing\n";
    throw new std::exception();
  }
  // isList
  if(nil->isList() != true){
    std::cerr << "Nil_test: unit test 2.1 failing\n";
    throw new std::exception();
  }

  // isInt
  if(nil->isInt() != false){
    std::cerr << "Nil_test: unit test 2.2 failing\n";
    throw new std::exception();
  }

  // isNil
  const Nil* nil2 = static_cast<const Nil*>(nil); // downcast
  if(nil2->isNil() != true){
    std::cerr << "Nil_test: unit test 2.3 failing\n";
    throw new std::exception();
  }

  // copy
  const Expression* copy = nil->copy();
  if(copy != nil){
    std::cerr << "Nil_test: unit test 3.0 failing\n";
    throw new std::exception();
  }

  Expression::destroy(copy);
  Expression::destroy(val);
  Expression::destroy(nil);
  delete env;
}

void ExpInt_test(){
  Environment* env = new Environment();
  const Expression* exp = new ExpInt(42);
  const ExpressionComposite* nil = new Nil();

  // eval
  const Expression* val = exp->eval(env);
  if(val != exp){
    std::cerr << "ExpInt_test: unit test 1.0 failing\n";
    throw new std::exception();
  }
  // apply
  try{
    exp->apply(nil);
    std::cerr << "ExpInt_test: unit test 1.1 failing\n";
  } catch(std::exception* e){
    // as expected
  }
  // toString
  if(exp->toString() != "42"){
    std::cerr << "ExpInt_test: unit test 2.0 failing\n";
    throw new std::exception();
  }
  // isList
  if(exp->isList() != false){
    std::cerr << "ExpInt_test: unit test 2.1 failing\n";
    throw new std::exception();
  }

  // isInt
  if(exp->isInt() != true){
    std::cerr << "ExpInt_test: unit test 2.2 failing\n";
    throw new std::exception();
  }

  // copy
  const Expression* copy = exp->copy();
  if(copy != exp){
    std::cerr << "ExpInt_test: unit test 3.0 failing\n";
    throw new std::exception();
  }

  Expression::destroy(copy);
  Expression::destroy(val);
  Expression::destroy(nil);
  Expression::destroy(exp);
  delete env;
}

void Plus_test(){
  Environment* env = new Environment();
  const Expression* plus = new Plus();
  const ExpressionComposite* nil = new Nil();

  // eval
  const Expression* val = plus->eval(env);
  if(val != plus){
    std::cerr << "Plus_test: unit test 1.0 failing\n";
    throw new std::exception();
  }
  // apply
  try{
    plus->apply(static_cast<const ExpressionComposite*>(nil));
    std::cerr << "Plus_test: unit test 1.1 failing\n";
  } catch(std::exception* e){
    // as expected  --------------------------------------------------------> TBI
  }
  // toString
  if(plus->toString() != "+"){
    std::cerr << "Plus_test: unit test 2.0 failing\n";
    throw new std::exception();
  }
  // isList
  if(plus->isList() != false){
    std::cerr << "Plus_test: unit test 2.1 failing\n";
    throw new std::exception();
  }

  // isInt
  if(plus->isInt() != false){
    std::cerr << "Plus_test: unit test 2.2 failing\n";
    throw new std::exception();
  }

   // copy
  const Expression* copy = plus->copy();
  if(copy != plus){
    std::cerr << "Plus_test: unit test 3.0 failing\n";
    throw new std::exception();
  }

  Expression::destroy(copy);
  Expression::destroy(val);
  Expression::destroy(nil);
  Expression::destroy(plus);
  delete env;
}

void Mult_test(){
  Environment* env = new Environment();
  const Expression* mult = new Mult();
  const ExpressionComposite* nil = new Nil();

  // eval
  const Expression* val = mult->eval(env);
  if(val != mult){
    std::cerr << "Mult_test: unit test 1.0 failing\n";
    throw new std::exception();
  }
  // apply
  try{
    mult->apply(static_cast<const ExpressionComposite*>(nil));
    std::cerr << "Mult_test: unit test 1.1 failing\n";
  } catch(std::exception* e){
    // as expected  --------------------------------------------------------> TBI
  }
  // toString
  if(mult->toString() != "*"){
    std::cerr << "Mult_test: unit test 2.0 failing\n";
    throw new std::exception();
  }
  // isList
  if(mult->isList() != false){
    std::cerr << "Mult_test: unit test 2.1 failing\n";
    throw new std::exception();
  }

  // isInt
  if(mult->isInt() != false){
    std::cerr << "Mult_test: unit test 2.2 failing\n";
    throw new std::exception();
  }

   // copy
  const Expression* copy = mult->copy();
  if(copy != mult){
    std::cerr << "Mult_test: unit test 3.0 failing\n";
    throw new std::exception();
  }

  Expression::destroy(copy);
  Expression::destroy(val);
  Expression::destroy(nil);
  Expression::destroy(mult);
  delete env;
}
int main(){

  /*
  Environment* env  = new Environment();
  Expression* two   = new ExpInt(2);
  Expression* seven = new ExpInt(7);
  Expression* five  = new ExpInt(5);
  Expression* plus  = new Plus();
  Expression* mult  = new Mult();
  Expression* exp1  = new Cons( // (+ 2 7 5)
                          plus,
                          new Cons(
                            two,
                            new Cons(
                              seven,
                              new Cons(
                                five,
                                new Nil()))));
  Expression* exp2  = new Cons( // (* 2 (+ 2 7 5) 5)
                          mult,
                          new Cons(
                            two->copy(), // copy to avoid multiple deallocation
                            new Cons(
                              exp1,
                              new Cons(
                                five->copy(), // idem
                                new Nil()))));

  std::cout << "The evaluation of the List Expression: " << exp2->toString();
  std::cout << "yields the value: " << exp2->eval(env);
  Expression::destroy(exp2);
  delete env;
  */
  return 0;
}

