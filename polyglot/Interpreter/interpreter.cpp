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
  // clone
  private:
    const _Exp* clone() const;
  // destructor
  protected:
    virtual ~_Exp(){}
  // new & delete override
  protected:
    void operator delete(void* ptr);
    void* operator new(size_t size);
    static void deallocate(const _Exp *ptr); // calls delete if refcount ==  zero 
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
    const _Exp* _left;
    const _Exp* _right;
  // constructors
  private:
    _And(const _Exp* left, const _Exp* right) : _left(left), _right(right) {}
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
    const _Exp* _left;
    const _Exp* _right;
  // constructors
  private:
    _Or(const _Exp* left, const _Exp* right) : _left(left), _right(right) {}
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
    const _Exp* _regex;
  // constructors
  private:
    _Many(const _Exp* regex) : _regex(regex) {}
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
//      std::cerr << std::hex << address << " : " << comment;
    }
    // adds pointer to 'mem_log' and logs 'message'
    static void log_new(void* address, std::string comment){
      assert(address != nullptr);
      assert(mem_log.find(address) == mem_log.end()); // must be unseen before
      mem_log.insert(address);  // adds pointer to 'mem_log'
      auto it = mem_log.find(address);  // looking for pointer now
      assert(it != mem_log.end());      // should be found
      assert(*it == address);           // should be what we expect
//      std::cerr << std::hex << address << " : " << comment;
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
  _Exp::deallocate(_impl);  // deletes pointer only if refcount down to zero
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

Exp Exp::And(const Exp& left, const Exp& right){
  return Exp(new _And(left._impl->clone(), right._impl->clone()));
}

Exp Exp::Or(const Exp& left, const Exp& right){
  return Exp(new _Or(left._impl->clone(), right._impl->clone()));
}

Exp Exp::Many(const Exp& regex){
  return Exp(new _Many(regex._impl->clone()));
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

void _Exp::deallocate(const _Exp *ptr){
  assert(ptr != nullptr);
  assert(ptr->refcount > 0);
  ptr->refcount--;
  if(ptr->refcount == 0){
    delete ptr;
  }
}

const _Exp* _Exp::clone() const{
  assert(refcount > 0);
  refcount++;
  return this;
}


/******************************************************************************/
/*                              _Lit Implementation                           */
/******************************************************************************/

_Lit::~_Lit(){}

std::string _Lit::to_string() const {
  return _literal;
}

List _Lit::interpret(std::string input) const {
  List result; 
  if(input.find(_literal) == 0){  // _literal is a prefix of input
    result.push_back(_literal);
  }
  return result;
}


/******************************************************************************/
/*                              _And Implementation                           */
/******************************************************************************/

_And::~_And(){
  _Exp::deallocate(_left);  // deletes pointer only if refcount down to zero
  _Exp::deallocate(_right); // deletes pointer only if refcount down to zero
}


std::string _And::to_string() const {
  return _left->to_string() + _right->to_string();
}

List _And::interpret(std::string input) const {}  // TODO


/******************************************************************************/
/*                              _Or Implementation                           */
/******************************************************************************/

_Or::~_Or(){
  _Exp::deallocate(_left);  // deletes pointer only if refcount down to zero
  _Exp::deallocate(_right); // deletes pointer only if refcount down to zero
}

std::string _Or::to_string() const {
  return "(" + _left->to_string() + "|" + _right->to_string() + ")";
}


List _Or::interpret(std::string input) const {}  // TODO



/******************************************************************************/
/*                              _Many Implementation                           */
/******************************************************************************/

_Many::~_Many(){
  _Exp::deallocate(_regex); // deletes pointer only if refcount down to zero
}

std::string _Many::to_string() const {
  return "(" + _regex->to_string() + ")*";
}

List _Many::interpret(std::string input) const {}  // TODO


/******************************************************************************/
/*                              Test Class                                    */
/******************************************************************************/

class Test{
  public:
    static int test_all();
    static int test_Exp();
    static int test__Exp();
    static int test__Lit();
    static int test__And();
    static int test__Or();
    static int test__Many();
};

int Test::test_all(){
  assert(!Log::has_memory_leak());
  assert(test_Exp() == 0);
  assert(test__Exp() == 0);
  assert(test__Lit() == 0);
  assert(test__And() == 0);
  assert(test__Or() == 0);
  assert(test__Many() == 0);
  assert(!Log::has_memory_leak());
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
  // we cannot check lack of memory leak at the stage
  // The stack allocated object 'e' should go out of scope
  // and be destroyed, thereby releasing pointer l1.
  // It is incumbent on another routine to check no 
  // mempry leak was created
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
  const _Lit* d1= static_cast<const _Lit*>(e1._impl);
  assert(d1->_literal == "abc");
  // Exp::And
  Exp e2 = Exp::Lit("def");
  assert(e2._impl != nullptr);
  assert(e2._impl->refcount == 1);
  const _Lit* d2 = static_cast<const _Lit*>(e2._impl); 
  assert(d2->_literal == "def");
  Exp e3 = Exp::And(e1, e2);
  assert(e3._impl != nullptr);
  assert(e3._impl->refcount == 1);
  const _And* d3 = static_cast<const _And*>(e3._impl);
  assert(d3->_left == e1._impl);
  assert(d3->_right == e2._impl);
  assert(e1._impl->refcount == 2);
  assert(e2._impl->refcount == 2);
  // Exp::Or
  Exp e4 = Exp::Or(e2, e3);
  assert(e4._impl != nullptr);
  assert(e4._impl->refcount == 1);
  const _Or* d4 = static_cast<const _Or*>(e4._impl);
  assert(d4->_left == e2._impl);
  assert(d4->_right == e3._impl);
  assert(e2._impl->refcount == 3);
  assert(e3._impl->refcount == 2);
  // Exp::Many
  Exp e5 = Exp::Many(e4);
  assert(e5._impl != nullptr);
  assert(e5._impl->refcount == 1);
  const _Many* d5 = static_cast<const _Many*>(e5._impl);
  assert(d5->_regex == e4._impl);
  assert(e4._impl->refcount == 2);
  // As stack allocated variables go out of scope, various pointers
  // will get deallocated. Testing for memory leaks need to occur
  // on this control path, but outside this method
  return 0;
}

int Test::test__Exp(){
  // new-delete
  assert(!Log::has_memory_leak());
  _Exp* e1 = new _Lit("abc");
  assert(Log::has_memory_leak());
  assert(e1 != nullptr);
  assert(e1->refcount == 1);
  delete e1;
  assert(!Log::has_memory_leak());
  // deallocate
  e1 = new _Lit("abc");
  assert(e1 != nullptr);
  assert(e1->refcount == 1);
  _Exp::deallocate(e1);
  assert(!Log::has_memory_leak());
  e1 = new _Lit("abc");
  assert(e1 != nullptr);
  assert(e1->refcount == 1);
  e1->refcount++;
  assert(e1->refcount == 2);
  _Exp::deallocate(e1);
  assert(e1->refcount == 1);
  _Exp::deallocate(e1);
  assert(!Log::has_memory_leak());
  // clone
  e1 = new _Lit("abc");
  assert(e1 != nullptr);
  assert(e1->refcount == 1);
  const _Exp* e2 = e1->clone(); 
  assert(e2 == e1);
  assert(e1->refcount == 2);
  delete e1;
  assert(!Log::has_memory_leak());

  return 0;
}


int Test::test__Lit(){
  // constructing on the heap
  assert(!Log::has_memory_leak());
  _Lit* lp = new _Lit("abc");
  assert(Log::has_memory_leak());
  assert(lp != nullptr);
  assert(lp->_literal == "abc");
  assert(lp->refcount == 1);
  assert(lp->to_string() == "abc");
  delete lp;
  assert(!Log::has_memory_leak());
  // contructing on the stack
  _Lit l("abc");
  assert(l.refcount == 1);
  assert(l._literal == "abc");
  assert(l.to_string() == "abc");
  assert(!Log::has_memory_leak());
 return 0;
}

int Test::test__And(){
  // construction from the heap
  assert(!Log::has_memory_leak());
  _Lit* l1 = new _Lit("abc");
  _Lit* l2 = new _Lit("def");
  _And* a = new _And(l1,l2);
  assert(a != nullptr);
  assert(a->refcount == 1);
  assert(a->_left == l1);
  assert(a->_right == l2);
  assert(a->to_string() == "abcdef");
  delete a;
  assert(!Log::has_memory_leak());
  // construction from the stack
  l1 = new _Lit("abc");
  l2 = new _Lit("def");
  _And b(l1,l2);
  assert(b.refcount == 1);
  assert(b._left == l1);
  assert(b._right == l2);
  assert(b.to_string() == "abcdef");
  // b goes out of scope, pointers l1 and l2 should get released
  // testing for memory leaks occurs outside of this method
 return 0;
}

int Test::test__Or(){
  // construction from the heap
  assert(!Log::has_memory_leak());
  _Lit* l1 = new _Lit("abc");
  _Lit* l2 = new _Lit("def");
  _Or* o = new _Or(l1,l2);
  assert(o != nullptr);
  assert(o->refcount == 1);
  assert(o->_left == l1);
  assert(o->_right == l2);
  assert(o->to_string() == "(abc|def)");
  delete o;
  assert(!Log::has_memory_leak());
  // construction from the stack
  l1 = new _Lit("abc");
  l2 = new _Lit("def");
  _Or p(l1,l2);
  assert(p.refcount == 1);
  assert(p._left == l1);
  assert(p._right == l2);
  assert(p.to_string() == "(abc|def)");
  // p goes out of scope, pointers l1 and l2 should get released
  // testing for memory leaks occurs outside of this method
  return 0;
}

int Test::test__Many(){
  // construction from the heap
  assert(!Log::has_memory_leak());
  _Lit* l = new _Lit("abc");
  _Many* m = new _Many(l);
  assert(m != nullptr);
  assert(m->refcount == 1);
  assert(m->_regex == l);
  assert(m->to_string() == "(abc)*");
  delete m;
  assert(!Log::has_memory_leak());
  // construction from the stack
  l = new _Lit("abc");
  _Many n(l);
  assert(n.refcount == 1);
  assert(n._regex == l);
  assert(n.to_string() == "(abc)*");
  // n goes out of scope, pointers l should get released
  // testing for memory leaks occurs outside of this method
 return 0;
}

/******************************************************************************/
/*                                 Main                                       */
/******************************************************************************/

int main(){

  assert(Test::test_all() == 0);

  assert(!Log::has_memory_leak());
  return 0;
}

