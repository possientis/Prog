// using dynamic cast to work out type of polymorphic objects
// type needs to be truly polymorphic, so make sure there is
// at least one virtual method.
#include <iostream>
#include <string>

class A{
  public:
    virtual void foo(){ std::cout << "A::foo running\n"; }
};

class B : public A {
  public:
    void foo() override { std::cout << "B::foo running\n"; }
};

class C : public B {
  public:
    void foo() override { std::cout << "C::foo running\n"; }
};

// key idea is that dynamic_cast returns nullptr in cases
// when downcast is inappropriate.

std::string get_type(A* obj){
  if(dynamic_cast<C*>(obj) != nullptr){       // downcast legal
    return "C";
  }
  else if(dynamic_cast<B*>(obj) != nullptr){  // downcast legal
      return "B";
  }
  else if(dynamic_cast<A*>(obj) != nullptr){  // downcast legal
    return "A";
  } else {
    return "nullptr";
  }
}

int main(){
  A* a = new A();
  B* b = new B();
  C* c = new C();

  std::cout << "Type of a is pointer to " << get_type(a) << std::endl;
  std::cout << "Type of b is pointer to " << get_type(b) << std::endl;
  std::cout << "Type of c is pointer to " << get_type(c) << std::endl;

  delete c;
  delete b;
  delete a;

  return 0;
}
