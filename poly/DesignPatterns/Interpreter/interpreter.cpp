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
  // API
  public:
    std::string to_string() const;
  // Given a string, this method returns 'the' list of all prefixes of the string
  // which belong to the language of the regular expression object. Of course,
  // such a list in only unique up to the order of its elements
    List interpret(std::string input) const;
    bool recognize(std::string input) const;
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
    bool recognize(std::string input) const;
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

std::string Exp::to_string() const {
  return _impl->to_string();
}

List Exp::interpret(std::string input) const {
  return _impl->interpret(input);
}

bool Exp::recognize(std::string input) const {
  return _impl->recognize(input);
}

std::ostream& operator<<(std::ostream& s, Exp exp){
  s << exp.to_string();
  return s;
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

bool _Exp::recognize(std::string input) const {
  List result = interpret(input);
  for(auto it = result.cbegin(); it != result.cend(); ++it){
    if(*it == input){ // found
      return true;
    }
  }
  return false;
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

List _And::interpret(std::string input) const {
  List result;
  assert(_left != nullptr);
  List left = _left->interpret(input); 
  for(auto it = left.cbegin(); it != left.cend(); ++it){
    std::string remainder = input.substr(it->length());
    assert(_right != nullptr);
    List right = _right->interpret(remainder);
    for(auto jt = right.cbegin(); jt != right.cend(); ++jt){
      result.push_back(*it + *jt);
    }
  }
  return result;
}



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


List _Or::interpret(std::string input) const {
  assert(_left != nullptr);
  List result = _left->interpret(input);
  assert(_right != nullptr);
  List right = _right->interpret(input);
  for(auto it = right.cbegin(); it != right.cend(); ++it){
    result.push_back(*it);
  }
  return result;
}



/******************************************************************************/
/*                              _Many Implementation                           */
/******************************************************************************/

_Many::~_Many(){
  _Exp::deallocate(_regex); // deletes pointer only if refcount down to zero
}

std::string _Many::to_string() const {
  return "(" + _regex->to_string() + ")*";
}

List _Many::interpret(std::string input) const {
  List result;
  result.push_back(""); // forall r:Exp, "" belongs to L(r*)
  assert(_regex != nullptr);
  List left = _regex->interpret(input);
  for(auto it = left.cbegin(); it != left.cend(); ++it){
    if(!it->empty()){
      std::string remainder = input.substr(it->length());
      List right = interpret(remainder);  // recursive call 
      for(auto jt = right.cbegin(); jt != right.cend(); ++jt){
        result.push_back(*it + *jt);
      }
    }
  }
  return result;
}


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
  // to_string
  Exp e6 = Exp::Lit("abc");
  Exp e7 = Exp::Lit("def");
  Exp e8 = Exp::And(e6,e7);
  Exp e9 = Exp::Or(e6,e7);
  Exp e10 = Exp::Many(e6);
  assert(e6.to_string() == "abc");
  assert(e7.to_string() == "def");
  assert(e8.to_string() == "abcdef");
  assert(e9.to_string() == "(abc|def)");
  assert(e10.to_string() == "(abc)*");
  // interpret
  List v6 = e6.interpret("abcx");
  List v7 = e7.interpret("defx");
  List v8 = e8.interpret("abcdefx");
  List v9 = e9.interpret("abcx");
  List v9_ = e9.interpret("defx");
  List v10 = e10.interpret("abcabcx");
  assert(v6.size() == 1);
  assert(v7.size() == 1);
  assert(v8.size() == 1);
  assert(v9.size() == 1);
  assert(v9_.size() == 1);
  assert(v10.size() == 3);
  assert(v6[0] == "abc");
  assert(v7[0] == "def");
  assert(v8[0] == "abcdef");
  assert(v9[0] == "abc");
  assert(v9_[0] == "def");
  assert(v10[0] == "");
  assert(v10[1] == "abc");
  assert(v10[2] == "abcabc");
  // recognize
  assert(e6.recognize("") == false);
  assert(e6.recognize("a") == false);
  assert(e6.recognize("ab") == false);
  assert(e6.recognize("abc") == true);
  assert(e6.recognize("abcx") == false);
  assert(e7.recognize("") == false);
  assert(e7.recognize("d") == false);
  assert(e7.recognize("de") == false);
  assert(e7.recognize("def") == true);
  assert(e7.recognize("defx") == false);
  assert(e8.recognize("") == false);
  assert(e8.recognize("a") == false);
  assert(e8.recognize("ab") == false);
  assert(e8.recognize("abc") == false);
  assert(e8.recognize("abcd") == false);
  assert(e8.recognize("abcde") == false);
  assert(e8.recognize("abcdef") == true);
  assert(e8.recognize("abcdefx") == false);
  assert(e9.recognize("") == false);
  assert(e9.recognize("a") == false);
  assert(e9.recognize("ab") == false);
  assert(e9.recognize("abc") == true);
  assert(e9.recognize("abcx") == false);
  assert(e9.recognize("d") == false);
  assert(e9.recognize("de") == false);
  assert(e9.recognize("def") == true);
  assert(e9.recognize("defx") == false);
  assert(e10.recognize("") == true);
  assert(e10.recognize("a") == false);
  assert(e10.recognize("ab") == false);
  assert(e10.recognize("abc") == true);
  assert(e10.recognize("abca") == false);
  assert(e10.recognize("abcab") == false);
  assert(e10.recognize("abcabc") == true);
  assert(e10.recognize("abcabca") == false);
  assert(e10.recognize("abcabcab") == false);
  assert(e10.recognize("abcabcabc") == true);
  assert(e10.recognize("abcabcabca") == false);
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
  List v1 = lp->interpret("");
  List v2 = lp->interpret("a");
  List v3 = lp->interpret("ab");
  List v4 = lp->interpret("abc");
  List v5 = lp->interpret("abcx");
  assert(v1.empty());
  assert(v2.empty());
  assert(v3.empty());
  assert(v4.size() == 1);
  assert(v5.size() == 1);
  assert(v4[0] == "abc");
  assert(v5[0] == "abc");
  delete lp;
  assert(!Log::has_memory_leak());
  // contructing on the stack
  _Lit l("abc");
  assert(l.refcount == 1);
  assert(l._literal == "abc");
  assert(l.to_string() == "abc");
  v1 = l.interpret("");
  v2 = l.interpret("a");
  v3 = l.interpret("ab");
  v4 = l.interpret("abc");
  v5 = l.interpret("abcx");
  assert(v1.empty());
  assert(v2.empty());
  assert(v3.empty());
  assert(v4.size() == 1);
  assert(v5.size() == 1);
  assert(v4[0] == "abc");
  assert(v5[0] == "abc");
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
  List v1 = a->interpret("");
  List v2 = a->interpret("a");
  List v3 = a->interpret("ab");
  List v4 = a->interpret("abc");
  List v5 = a->interpret("abcd");
  List v6 = a->interpret("abcde");
  List v7 = a->interpret("abcdef");
  List v8 = a->interpret("abcdefx");
  assert(v1.empty());
  assert(v2.empty());
  assert(v3.empty());
  assert(v4.empty());
  assert(v5.empty());
  assert(v6.empty());
  assert(v7.size() == 1);
  assert(v8.size() == 1);
  assert(v7[0] == "abcdef");
  assert(v8[0] == "abcdef");
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
  v1 = b.interpret("");
  v2 = b.interpret("a");
  v3 = b.interpret("ab");
  v4 = b.interpret("abc");
  v5 = b.interpret("abcd");
  v6 = b.interpret("abcde");
  v7 = b.interpret("abcdef");
  v8 = b.interpret("abcdefx");
  assert(v1.empty());
  assert(v2.empty());
  assert(v3.empty());
  assert(v4.empty());
  assert(v5.empty());
  assert(v6.empty());
  assert(v7.size() == 1);
  assert(v8.size() == 1);
  assert(v7[0] == "abcdef");
  assert(v8[0] == "abcdef");
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
  List v1 = o->interpret("");
  List v2 = o->interpret("a");
  List v3 = o->interpret("ab");
  List v4 = o->interpret("abc");
  List v5 = o->interpret("abcx");
  List v6 = o->interpret("d");
  List v7 = o->interpret("de");
  List v8 = o->interpret("def");
  List v9 = o->interpret("defx");
  assert(v1.empty());
  assert(v2.empty());
  assert(v3.empty());
  assert(v6.empty());
  assert(v7.empty());
  assert(v4.size() == 1);
  assert(v5.size() == 1);
  assert(v8.size() == 1);
  assert(v9.size() == 1);
  assert(v4[0] == "abc"); 
  assert(v5[0] == "abc"); 
  assert(v8[0] == "def"); 
  assert(v9[0] == "def"); 
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
  List v1 = m->interpret("");
  List v2 = m->interpret("a");
  List v3 = m->interpret("ab");
  List v4 = m->interpret("abc");
  List v5 = m->interpret("abca");
  List v6 = m->interpret("abcab");
  List v7 = m->interpret("abcabc");
  List v8 = m->interpret("abcabca");
  List v9 = m->interpret("abcabcab");
  List v10 = m->interpret("abcabcabc");
  List v11 = m->interpret("abcabcabca");
  List v12 = m->interpret("abcabcabcab");
  assert(v1.size() == 1);
  assert(v2.size() == 1);
  assert(v3.size() == 1);
  assert(v4.size() == 2);
  assert(v5.size() == 2);
  assert(v6.size() == 2);
  assert(v7.size() == 3);
  assert(v8.size() == 3);
  assert(v9.size() == 3);
  assert(v10.size() == 4);
  assert(v11.size() == 4);
  assert(v12.size() == 4);
  assert(v1[0] == "");
  assert(v2[0] == "");
  assert(v3[0] == "");
  assert(v4[0] == "");
  assert(v5[0] == "");
  assert(v6[0] == "");
  assert(v7[0] == "");
  assert(v8[0] == "");
  assert(v9[0] == "");
  assert(v10[0] == "");
  assert(v11[0] == "");
  assert(v12[0] == "");
  assert(v4[1] == "abc");
  assert(v5[1] == "abc");
  assert(v6[1] == "abc");
  assert(v7[1] == "abc");
  assert(v8[1] == "abc");
  assert(v9[1] == "abc");
  assert(v10[1] == "abc");
  assert(v11[1] == "abc");
  assert(v12[1] == "abc");
  assert(v7[2] == "abcabc");
  assert(v8[2] == "abcabc");
  assert(v9[2] == "abcabc");
  assert(v10[2] == "abcabc");
  assert(v11[2] == "abcabc");
  assert(v12[2] == "abcabc");
  assert(v10[3] == "abcabcabc");
  assert(v11[3] == "abcabcabc");
  assert(v12[3] == "abcabcabc");
  delete m;
  assert(!Log::has_memory_leak());
  // construction from the stack
  l = new _Lit("abc");
  _Many n(l);
  assert(n.refcount == 1);
  assert(n._regex == l);
  assert(n.to_string() == "(abc)*");
  v1 = n.interpret("");
  v2 = n.interpret("a");
  v3 = n.interpret("ab");
  v4 = n.interpret("abc");
  v5 = n.interpret("abca");
  v6 = n.interpret("abcab");
  v7 = n.interpret("abcabc");
  v8 = n.interpret("abcabca");
  v9 = n.interpret("abcabcab");
  v10 = n.interpret("abcabcabc");
  v11 = n.interpret("abcabcabca");
  v12 = n.interpret("abcabcabcab");
  assert(v1.size() == 1);
  assert(v2.size() == 1);
  assert(v3.size() == 1);
  assert(v4.size() == 2);
  assert(v5.size() == 2);
  assert(v6.size() == 2);
  assert(v7.size() == 3);
  assert(v8.size() == 3);
  assert(v9.size() == 3);
  assert(v10.size() == 4);
  assert(v11.size() == 4);
  assert(v12.size() == 4);
  assert(v1[0] == "");
  assert(v2[0] == "");
  assert(v3[0] == "");
  assert(v4[0] == "");
  assert(v5[0] == "");
  assert(v6[0] == "");
  assert(v7[0] == "");
  assert(v8[0] == "");
  assert(v9[0] == "");
  assert(v10[0] == "");
  assert(v11[0] == "");
  assert(v12[0] == "");
  assert(v4[1] == "abc");
  assert(v5[1] == "abc");
  assert(v6[1] == "abc");
  assert(v7[1] == "abc");
  assert(v8[1] == "abc");
  assert(v9[1] == "abc");
  assert(v10[1] == "abc");
  assert(v11[1] == "abc");
  assert(v12[1] == "abc");
  assert(v7[2] == "abcabc");
  assert(v8[2] == "abcabc");
  assert(v9[2] == "abcabc");
  assert(v10[2] == "abcabc");
  assert(v11[2] == "abcabc");
  assert(v12[2] == "abcabc");
  assert(v10[3] == "abcabcabc");
  assert(v11[3] == "abcabcabc");
  assert(v12[3] == "abcabcabc");
  // n goes out of scope, pointers l should get released
  // testing for memory leaks occurs outside of this method
 return 0;
}

/******************************************************************************/
/*                                 Main                                       */
/******************************************************************************/

static void print(List l){
  bool start = true;
  std::cout << "[";
  for(auto it = l.cbegin(); it != l.cend(); ++it){
    if(start){
      start = false;
    } else {
      std::cout << ", ";
    }
    std::cout << *it;
  }
  std::cout << "]\n";
}

static int run(){
  Exp a = Exp::Lit("a"); 
  Exp b = Exp::Lit("b");
  Exp c = Exp::Lit("c");
  
  Exp aa = Exp::And(a, Exp::Many(a)); // one or more 'a'
  Exp bb = Exp::And(b, Exp::Many(b)); // one or more 'b'
  Exp cc = Exp::And(c, Exp::Many(c)); // one or more 'c'

  Exp regex = Exp::Many(Exp::And(Exp::Or(aa,bb), cc));
  std::string str = "acbbccaaacccbbbbaaaaaccccc";

  std::cout << "regex = " << regex << std::endl;
  std::cout << "string = \"" << str << "\"\n";
  std::cout << "The recognized prefixes are:\n";

  List result;
  for(int i = 0; i <= str.length(); ++i){
    std::string test = str.substr(0,i);
    if(regex.recognize(test)){
      result.push_back("\"" + test + "\"");
    }
  }

  print(result);

  return 0;
}

int main(){
//  assert(Test::test_all() == 0);
  assert(run() == 0);
  assert(!Log::has_memory_leak());
  return 0;
}

