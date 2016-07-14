// Interpreter Design Pattern
#include <iostream>
#include <string>
#include <vector>
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
//  - r = Lit(s)        -> L(r) = {s}
//  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
//  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
//  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
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

typedef std::vector<std::string> List;

class Exp {
  private:
    int refcount;
  protected:
    Exp() : refcount(1) {}
  public:
    virtual ~Exp(){}
    virtual std::string to_string() const =0;
    virtual List interpret(std::string input) const =0;
    bool recognize(std::string input) const;  // TODO
    Exp* copy(){ refcount++; return this; }
};



class Lit : public Exp {
  friend Exp* makeLit(std::string);
  private:
    std::string _literal;
    Lit(std::string literal) : _literal(literal) {}
  public:
    ~Lit();                                       // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

class And : public Exp {
  private:
    Exp* _left;
    Exp* _right;
  protected:
    And(Exp* left, And* right) : _left(left), _right(right) {}
  public:
    ~And();                                       // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

class Or : public Exp {
  private:
    Exp* _left;
    Exp* _right;
  protected:
    Or(Exp* left, Exp* right) : _left(left), _right(right) {}
  public:
    ~Or();                                        // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};

class Many : public Exp {
  private:
    Exp* _regex;
  protected:
    Many(Exp* regex) : _regex(regex) {}
  public:
    ~Many();                                      // TODO
    std::string to_string() const override;       // TODO
    List interpret(std::string) const override;   // TODO
};


Lit::~Lit(){}
std::string Lit::to_string() const {}
List Lit::interpret(std::string input) const {}
Exp* makeLit(std::string literal){
  return new Lit(literal);
}



int main(){

  return 0;
}


