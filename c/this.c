// This is important when implementing the visitor pattern.
// If you have a base method whose code involves 'this', the
// 'this' pointer may not be aware it is pointing to a derived
// object. Hence, not only do you need to declare your method
// virtual, but you also need to provide an override for that
// method, despite the fact it has formally identical code.

#include<iostream>

using namespace std;
class A;
class B;

static void visit(const A& a){cout << "This is an base object\n";}
static void visit(const B& b){cout << "This is a derived object\n";}

class A {
  public:
    long x;
    // not declared virtual
    void foo(){visit(*this);}
    // declared virtual but no override provided
    virtual void bar() {visit(*this);}
    // declared virtual with formally identical override code
    virtual void baz() {visit(*this);}
};

class B : public A {
  public:
    long y;
    // override has same code as base class version
    virtual void baz() {visit(*this);}
};

int main()
{

  A a;
  B b;

  visit(a);
  visit(b);


  A* pa = new A();
  A* pb = new B();

  cout << "Calling non-virtual foo\n";

  pa->foo();
  pb->foo();

  cout << "Calling virtual bar (which has no override)\n";

  pa->bar();
  pb->bar();

  cout << "Calling virtual baz (which has an override)\n";
  pa-> baz();
  pb->baz();

  delete pa;
  delete pb;

}
