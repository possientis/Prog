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
  /*
   * DO NOT FORGET TO DECLARE DESTRUCTOR 'virtual' or else destruction
   * of pointers to Base objects (which are really pointers to some
   * derived object) will not be carried out properly. Toggle the keyword
   * 'virtual' on and off and see output of program
   *
   * It seems like declaring constructor to be pure virtual (= 0) makes
   * no difference, as long as an implementation is still provided
   *
   * Even if not declared pure (and Lakos says it should not be), you
   * still need to provide an implementation (inline or out-of-line).
   * However, it is best to have implementation out-of-line so compiler
   * knows in which translation unit to include vtable of base class.
   * Otherwise, Base class has no implementation outside of header file
   * and it is not clear what compiler should do when that header file
   * is included in several translation units.
   */
  virtual ~Base() /* = 0 */;  // virtual, but not pure virtual and not inline
  virtual void foo()=0;   // pure virtual
};

class Derived : public Base {

  public:
  Derived(){std::cout << "running derived constructor\n";}
  // 'virtual' keyword in implementation class seems optional but probably
  // has impact on futher subclasses. It increases readability anyway.
  virtual ~Derived(){std::cout << "running derived destructor\n";}
  virtual void foo(){ std::cout << "running implementation of foo\n";}
};


int main()
{
  std::cout << "-------- Automatic object ---------\n";
  std::cout << "\ncreating derived object...\n";
  Derived b;

  std::cout << "\ncalling foo method on object...\n";
  b.foo();

  std::cout << "\n--------- Pointer to Derived -------\n";
  std::cout << "\nallocating new Derived* pointer\n";
  Derived* p = new Derived;

  std::cout << "\ncalling foo method on Derived* pointer\n";
  p->foo();

  std::cout << "\nde-allocating Derived* pointer\n";
  delete p;

  std::cout << "\n---------- Pointer to Base ---------\n";
  std::cout << "\nallocating new Base* pointer\n";
  Base* q = new Derived;

  std::cout << "\ncalling foo method on Base* pointer\n";
  q->foo();

  std::cout << "\nde-allocating Base* pointer\n";
  delete q;

  std::cout << "\n--------- Terminating ---------------\n";

}



Base::~Base()
{
  // not an empty implementation but almost...
  std::cout << "running base destructor\n";
}

