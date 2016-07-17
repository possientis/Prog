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
    _Exp* _impl;
  // constructors
  private:
    Exp(_Exp* impl);
  public:
    Exp(const Exp& rhs);
  // destructor
  public:
    ~Exp();
  // factory functions
  public:
    static Exp Lit(std::string literal);
  // assignment
  public:
    Exp& operator=(Exp rhs);
  //swap
  private:
    void swap(Exp& e1, Exp& e2);
};
  
/******************************************************************************/
/*                               _Exp Class                                   */
/******************************************************************************/

class _Exp {
  friend Test;
  friend Exp; 
  private:
    int refcount;
  protected:
    _Exp() : refcount(1) {}
  public:
    void operator delete(void* ptr);
    void* operator new(size_t size);
    virtual ~_Exp(){}
    virtual std::string to_string() const =0;
    virtual List interpret(std::string input) const =0;
    bool recognize(std::string input) const;  // TODO
};


/******************************************************************************/
/*                               _Lit Class                                   */
/******************************************************************************/

class _Lit : public _Exp {
  friend Test;
  friend Exp;
  private:
    std::string _literal;
    _Lit(std::string literal) : _literal(literal) {}
  public:
    ~_Lit();                                      
    std::string to_string() const override;       
    List interpret(std::string) const override;  
};

/******************************************************************************/
/*                              _And Class                                    */
/******************************************************************************/

class _And : public _Exp {
  private:
    _Exp* _left;
    _Exp* _right;
  protected:
    _And(_Exp* left, _And* right) : _left(left), _right(right) {}
  public:
    ~_And();                                      // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

/******************************************************************************/
/*                               _Or Class                                    */
/******************************************************************************/

class _Or : public _Exp {
  private:
    _Exp* _left;
    _Exp* _right;
  protected:
    _Or(_Exp* left, _Exp* right) : _left(left), _right(right) {}
  public:
    ~_Or();                                       // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

/******************************************************************************/
/*                             _Many Class                                    */
/******************************************************************************/

class _Many : public _Exp {
  private:
    _Exp* _regex;
  protected:
    _Many(_Exp* regex) : _regex(regex) {}
  public:
    ~_Many();                                     // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

/******************************************************************************/
/*                               Log Class                                    */
/******************************************************************************/

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
  } else {
  }
}

Exp::Exp(_Exp* impl) : _impl(impl) {} 

Exp::Exp(const Exp& rhs) : _impl(rhs._impl){
  assert(_impl != nullptr);
  _impl->refcount++;
}

void Exp::swap(Exp& e1, Exp& e2){
  std::swap<_Exp*>(e1._impl,e2._impl);
}

Exp& Exp::operator=(Exp rhs){
  swap(*this, rhs);
  return *this;
}

Exp Exp::Lit(std::string literal){
  return Exp(new _Lit(literal));
}


/******************************************************************************/
/*                          _Exp Implementation                               */
/******************************************************************************/

void* _Exp::operator new(size_t size){
  void* ptr = ::operator new(size);
  Log::log_new(ptr, "Allocating new pointer to _Exp object\n");
  return ptr;
}

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
/*                              Test Class                                    */
/******************************************************************************/

class Test{
  public:
    static int test_all();
    static int test_Lit();
};


int Test::test_Lit(){
  Exp l1 = Exp::Lit("abc");
  assert(l1._impl != nullptr);
  assert(l1._impl->refcount == 1);
  _Lit* derived = static_cast<_Lit*>(l1._impl);
  assert(derived->_literal == "abc");
  Exp l2 = l1;
  assert(l1._impl == l2._impl);
  assert(l1._impl->refcount == 2);
  l1 = l1;
  assert(l1._impl == l2._impl);
  assert(l1._impl->refcount == 2);
  l1 = l2;
  assert(l1._impl == l2._impl);
  assert(l1._impl->refcount == 2);
  Exp l3 = Exp::Lit("def");
  return 0;
}

int Test::test_all(){
  assert(!Log::has_memory_leak());
  assert(test_Lit() == 0);
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

