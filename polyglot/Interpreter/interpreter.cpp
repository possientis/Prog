// Interpreter Design Pattern
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <assert.h>
// from the Gang of Four book:
// "If a particular kind of problem occurs often enough, then it might be
// worthwhile to express instances of the problem as sentences in a simple
// language. Then you can build an interpreter that solves the problem by 
// interpreting these sentences. For example, searching for strings that 
// match a pattern is a common problem. Regular expressions are a standard 
// language for specifying patterns of strings. Rather than building custom 
// algorithms to match each pattern against strings, search algorithms could 
// interpret a regular expression that specifies a set of strings to match."

// Each regular expression r has an associated language L(r) (which is a set
// of strings) defined by the recursion:
//
//  - r = _Lit(s)        -> L(r) = {s}
//  - r = _And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
//  - r = _Or(r1, r2)    -> L(r) = L(r1) U L(r2)
//  - r = _Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
//
//  where given A,B sets of strings the product A.B is defined as the set of 
//  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
//  A^0 = {""} and A^1 = A. 
//
// Given a regular expression r and a string s, many reasonable questions 
// can be asked in relation to r and s. When using the command 'grep', the
// question being asked is whether there exist a substring s' of s which
// belongs to the language of r. One of the first questions of interest is
// of course whether s itself belongs to L(r).


class Test;
class _Exp;

typedef std::vector<std::string> List;

/******************************************************************************/
/*                                Exp Class                                   */
/******************************************************************************/

class Exp {
  // friends
    friend Test;
  // data
  private:
    const _Exp* _impl;
  // constructors
  private:
    Exp(const _Exp* impl);
  public:
    Exp(const Exp& rhs);
  // destructor
  public:
    ~Exp();
  // factory functions
  public:
    static Exp Lit(std::string literal);
    static Exp And(const Exp& left, const Exp& right);
    static Exp Or(const Exp& left, const Exp& right);
    static Exp Many(const Exp& regex);
  // assignment
  public:
    Exp& operator=(Exp rhs);
  //swap
  private:
    static void swap(Exp& e1, Exp& e2);
};
  
/******************************************************************************/
/*                               _Exp Class                                   */
/******************************************************************************/

class _Exp {
  // friends
    friend Test;
    friend Exp; 
  // data
  protected:
    mutable int refcount;
  // constructors
  protected:
    _Exp() : refcount(1) {}
  private:
    _Exp(const _Exp&);  // not implemented
  // destructor
  protected:
    virtual ~_Exp(){}
  // new & delete override
  protected:
    void operator delete(void* ptr);
    void* operator new(size_t size);
  // API
  public:
    virtual std::string to_string() const =0;
    virtual List interpret(std::string input) const =0;
    bool recognize(std::string input) const;  // TODO
};


/******************************************************************************/
/*                               _Lit Class                                   */
/******************************************************************************/

class _Lit : public _Exp {
  // friends
    friend Test;
    friend Exp;
  // data
  private:
    const std::string _literal;
  // constructors
  private:
    _Lit(std::string literal) : _literal(literal) {}
    _Lit(const _Lit&);            // not implemented
  //assignment
  private:
    _Lit& operator=(const _Lit&); // not implemented 
  // destructor
  private:
    ~_Lit();                                      
  // API
  private:
    std::string to_string() const override;       
    List interpret(std::string) const override;  
};

/******************************************************************************/
/*                              _And Class                                    */
/******************************************************************************/

class _And : public _Exp {
  // friends
    friend Test;
    friend Exp;
  // data
  private:
    _Exp* _left;
    _Exp* _right;
  // constructors
  private:
    _And(_Exp* left, _And* right) : _left(left), _right(right) {}
    _And(const _And&);            // not implemented
  // assignment
  private:
    _And& operator=(const _And&); // not implemented
  // destructor
  private:
    ~_And();                                      
  // API
  private:
    std::string to_string() const override;       
    List interpret(std::string) const override;   
};

/******************************************************************************/
/*                               _Or Class                                    */
/******************************************************************************/

class _Or : public _Exp {
  // friends
    friend Test;
    friend Exp;
  // data
  private:
    _Exp* _left;
    _Exp* _right;
  // constructors
  private:
    _Or(_Exp* left, _Exp* right) : _left(left), _right(right) {}
    _Or(const _Or&);            // not implemented
  // assignment
  private:
    _Or& operator=(const _Or&); // not implemented
  // destructor
  private:
    ~_Or();                                       
  // API
  private:
    std::string to_string() const override;       
    List interpret(std::string) const override;   
};

/******************************************************************************/
/*                             _Many Class                                    */
/******************************************************************************/

class _Many : public _Exp {
  // friends
  friend Test;
  friend Exp;
  // data
  private:
    _Exp* _regex;
  // constructors
  private:
    _Many(_Exp* regex) : _regex(regex) {}
    _Many(const _Many&);            // not implemented
  // assignment
  private:
    _Many& operator=(const _Many&); // not implemented
  // destructor
  private:
    ~_Many();                                     
  // API
  private:
    std::string to_string() const override;       
    List interpret(std::string) const override;   
};

/******************************************************************************/
/*                               Log Class                                    */
/******************************************************************************/

// This class manages a set of previously allocated pointers, so as to ensure
// every allocated pointers gets deallocated.
class Log {
  private:
    // set of pointers declared with 'log_new'
    static std::set<void*> mem_log;
  public:
    // removes pointer from 'mem_log' and logs 'message'
    static void log_delete(void* address, std::string comment){
      assert(address != nullptr);
      auto it = mem_log.find(address);
      assert(it != mem_log.end());  // can't delete unless previously allocated
      mem_log.erase(it);            // removes pointer from 'mem_log'
      assert(mem_log.find(address) == mem_log.end()); // should be gone
      std::cerr << std::hex << address << " : " << comment;
    }
    // adds pointer to 'mem_log' and logs 'message'
    static void log_new(void* address, std::string comment){
      assert(address != nullptr);
      assert(mem_log.find(address) == mem_log.end()); // must be unseen before
      mem_log.insert(address);  // adds pointer to 'mem_log'
      auto it = mem_log.find(address);  // looking for pointer now
      assert(it != mem_log.end());      // should be found
      assert(*it == address);           // should be what we expect
      std::cerr << std::hex << address << " : " << comment;
    }
    static bool has_memory_leak(){
      return !mem_log.empty();
    }
};

std::set<void*> Log::mem_log;

/******************************************************************************/
/*                            Exp Implementation                              */
/******************************************************************************/

Exp::~Exp(){
  assert(_impl != nullptr);
  assert(_impl->refcount > 0);
  _impl->refcount--;
  if(_impl->refcount == 0){
    delete _impl;
  }
}

Exp::Exp(const _Exp* impl) : _impl(impl) {} 

Exp::Exp(const Exp& rhs) : _impl(rhs._impl){
  assert(_impl != nullptr);
  _impl->refcount++;
}

void Exp::swap(Exp& e1, Exp& e2){
  std::swap<const _Exp*>(e1._impl,e2._impl);
}

Exp& Exp::operator=(Exp rhs){ // copy constructor invoked, argument by value
  swap(*this, rhs);
  return *this;
}

Exp Exp::Lit(std::string literal){
  return Exp(new _Lit(literal));
}

Exp Exp::And(const Exp& left, const Exp& right){  // TODO
}

Exp Exp::Or(const Exp& left, const Exp& right){   // TODO
}

Exp Exp::Many(const Exp& regex){                  // TODO
}


/******************************************************************************/
/*                          _Exp Implementation                               */
/******************************************************************************/

// operator new is overriden to ensure logging takes place
void* _Exp::operator new(size_t size){
  void* ptr = ::operator new(size);
  Log::log_new(ptr, "Allocating new pointer to _Exp object\n");
  return ptr;
}

// operator delete is overriden to ensure logging takes place
void _Exp::operator delete(void* ptr){
  Log::log_delete(ptr, "Deallocating pointer to _Exp object\n");
  ::operator delete(ptr);
}

/******************************************************************************/
/*                              _Lit Implementation                           */
/******************************************************************************/

_Lit::~_Lit(){}

std::string _Lit::to_string() const {}            // TODO

List _Lit::interpret(std::string input) const {}  // TODO


/******************************************************************************/
/*                              _And Implementation                           */
/******************************************************************************/

_And::~_And(){
  assert(_left != nullptr);
  assert(_left->refcount > 0);
}


std::string _And::to_string() const {}            // TODO

List _And::interpret(std::string input) const {}  // TODO


/******************************************************************************/
/*                              _Or Implementation                           */
/******************************************************************************/

_Or::~_Or(){}

std::string _Or::to_string() const {}            // TODO

List _Or::interpret(std::string input) const {}  // TODO



/******************************************************************************/
/*                              _Many Implementation                           */
/******************************************************************************/

_Many::~_Many(){}

std::string _Many::to_string() const {}            // TODO

List _Many::interpret(std::string input) const {}  // TODO


/******************************************************************************/
/*                              Test Class                                    */
/******************************************************************************/

class Test{
  public:
    static int test_all();
    static int test_Exp();
    static int test__Lit();
};

int Test::test_all(){
  assert(test_Exp() == 0);
  assert(test__Lit() == 0);
  return 0;
}

int Test::test_Exp(){
  // constructing from the heap
  assert(!Log::has_memory_leak());
  _Lit* l2 = new _Lit("def");
  Exp* ep = new Exp(l2);
  assert(ep != nullptr);
  assert(ep->_impl == l2);
  delete ep;
  assert(!Log::has_memory_leak());
  // constructing on the stack
  _Lit* l1 = new _Lit("abc");
  assert(Log::has_memory_leak());
  assert(l1 != nullptr);
  Exp e(l1);
  assert(e._impl == l1);
  // copy constructor
  Exp f(e);
  assert(f._impl == e._impl);
  assert(f._impl == l1);
  assert(l1->refcount == 2);
  // swap
  l2 = new _Lit("def");
  Exp g(l2);
  Exp::swap(f,g);
  assert(f._impl == l2);
  assert(g._impl == l1);
  assert(l2->refcount == 1);
  assert(l1->refcount == 2);
  // assignment
  g = f;
  assert(f._impl == l2);
  assert(g._impl == l2);
  assert(l2->refcount == 2);
  assert(l1->refcount == 1);
  g = g;
  assert(g._impl == l2);
  assert(l2->refcount == 2);
  e = g;
  assert(g._impl == l2);
  assert(e._impl == l2);
  assert(l2->refcount == 3);
  // Exp::Lit
  Exp e1 = Exp::Lit("abc");
  assert(e1._impl != nullptr);
  assert(e1._impl->refcount == 1);
  const _Lit* derived = static_cast<const _Lit*>(e1._impl);
  assert(derived->_literal == "abc");

  return 0;
}


int Test::test__Lit(){
  // contructing on the stack
  _Lit l("abc");
  assert(l.refcount == 1);
  assert(l._literal == "abc");
  // constructing on the heap
  assert(!Log::has_memory_leak());
  _Lit* lp = new _Lit("abc");
  assert(Log::has_memory_leak());
  assert(lp != nullptr);
  assert(lp->_literal == "abc");
  assert(lp->refcount == 1);
  delete lp;
  assert(!Log::has_memory_leak());

 return 0;
}




/******************************************************************************/
/*                                 Main                                       */
/******************************************************************************/

int main(){

  assert(Test::test_all() == 0);

  return 0;
}

