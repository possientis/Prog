// Actually, this is fine. This 'this' pointer is aware that it is referring
// to a derived object.


// This is important when implementing the visitor pattern.
// If you have a base method whose code involves 'this', the
// 'this' pointer may not be aware it is pointing to a derived
// object. Hence, not only do you need to declare your method
// virtual, but you also need to provide an override for that
// method, despite the fact it has formally identical code.

#include<iostream>

class A;
class B;

static void visit(A* a);
class A {
  public:
    // type signature
    virtual void type(){ std::cout << "This is an A object\n"; }
    // not declared virtual
    void foo(){visit(this);}
    // declared virtual but no override provided
    virtual void bar() {visit(this);}
    // declared virtual with formally identical override code
    virtual void baz() {visit(this);}
};

class B : public A {
  public:
    void type() override { std::cout << "This is a B object\n"; }
    // override has same code as base class version
    virtual void baz() {visit(this);}
};

static void visit(A* a){ a->type(); }
static void visit(B* b){ b->type();}

int main()
{

  A a;
  B b;

  visit(&a);
  visit(&b);


  A* pa = new A();
  A* pb = new B();

  std::cout << "Calling non-virtual foo\n";

  pa->foo();
  pb->foo();

  std::cout << "Calling virtual bar (which has no override)\n";

  pa->bar();
  pb->bar();

  std::cout << "Calling virtual baz (which has an override)\n";
  pa-> baz();
  pb->baz();

  delete pa;
  delete pb;

}
