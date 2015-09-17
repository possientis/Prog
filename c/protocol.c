#include<iostream>

// protocol class as per John lakos page 386
// 1. It does not contain member data (or inherit from classes which do)
// 2. It does not have non-virtual methods (or inherit from classes which do)
// (with the exception of the constructor which cannot be declared virtual)
// 3. It does not have private (or protected) member (or inherit from
// classes which do)
// 4. destructor should be a. virtual (see 2.) b. non-inline and c. with
// an empty implementation
// 5. all members function should be pure virtual (except constructor which
// cannot be virtual)
// and the destructor which should not be pure (it should have an empty
// implementation)

/*
 * In short, in a protocol class:
 * 1. Everything should be public
 * 2. Everything should be virtual (except the constructor)
 * 3. Everything should be pure (except destructor with non-inline empty implementation)
 */


class Base {
  public: // everything is public
  Base(){std::cout << "running base constructor\n";}  // never virtual
  virtual ~Base();  // virtual, but not pure virtual and not inline
  virtual void foo()=0;   // pure virtual
};

class Derived : public Base {

  public:
  Derived(){std::cout << "running derived constructor\n";}
  ~Derived(){std::cout << "running derived destructor\n";}
  void foo(){ std::cout << "running implementation of foo\n";}
};


int main()
{
  std::cout << "\ncreating derived object...\n";
  Derived b;

  std::cout << "\ncalling foo method on object...\n";
  b.foo();

  std::cout << "\nallocating new Derived* pointer\n";
  Derived* p = new Derived;

  std::cout << "\ncalling foo method on Derived* pointer\n";
  p->foo();

  std::cout << "\nde-allocating Derived* pointer\n";
  delete p;

  std::cout << "\nallocating new Base* pointer\n";
  Base* q = new Derived;

  std::cout << "\ncalling foo method on Base* pointer\n";
  q->foo();

  std::cout << "\nde-allocating Base* pointer\n";
  delete q;

  std::cout << "\nterminating program...\n";

}






Base::~Base()
{
  // not an empty implementation but almost...
  std::cout << "running base destructor\n";
}

