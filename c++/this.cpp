// The purpose of this test file is to determine once and for all
// whether 'this' appearing in base class code is aware of the 
// fact it is pointing to a derived object.

// As far as we can tell, 'this' knows it is referring to derived object.
//
// 'this' KNOWS IT IS REFERRING TO DERIVED OBJECT IN BASE CODE
//
// but be careful with overloaded functions baz(Base*), baz(Derived*)
// which are statically linked, so if you call baz(this), the run-time
// type of *this does not matter. 


#include <iostream>
class A;
class B;

void baz(A*);
void baz(B*);

class A {
  public:
    virtual ~A(){}  // just to create polymorphic type
    void foo(){ this->bar(); }
    virtual void bar(){ std::cout << "A::bar is running\n"; }
    // BEWARE !!!!!!!!!!!!
    // compiler will link to baz(A*). The decision to run baz(A*)
    // or baz(B*) is not made at run time (why should it, baz is not
    // a virtual method or anything, just an overloaded function)
    // so, eventhough this may happen to refer to a derived object,
    // this derived object will be passed as argument to baz(A*)
    void warning(){ baz(this); }  
};

class B : public A {
  public:
    void bar() override { std::cout << "B::bar is running\n"; }
};


void baz(A* a){
  std::cout << "void baz(A*) is called while "; a->bar();
}

void baz(B* a){
  std::cout << "void baz(B*) is called while "; a->bar();
}

int main(){

  A* a = new A();
  a->foo(); // calling A::bar, no surprises here
  A* b = new B();
  b->foo(); // calling B::bar, so 'this' is derived-aware.

  a->warning(); // be very careful
  b->warning(); // be very careful, baz(B*) is not called, but still B object

  return 0;
}
