#include <iostream>

class A {
  public:
    virtual ~A(){}  // just to create polymorphic type
    virtual A* foo(){ return this; }
    virtual void bar(){ std::cout << "A::bar is running\n"; }
};

class B : public A {
  public:
    void bar() override { std::cout << "B::bar is running\n"; }
};


int main(){

  A a;
  A* ptr = a.foo();
  if(dynamic_cast<A*>(ptr)){
    std::cout << "ptr is pointer to A\n";
  }
  if(dynamic_cast<B*>(ptr)){  // won't happen
    std::cout << "ptr is also pointer to B\n";
  }

  ptr->bar();

  B b;
  A* qtr = b.foo();
  if(dynamic_cast<A*>(qtr)){
    std::cout << "qtr is pointer to A\n";
  }

  if(dynamic_cast<B*>(qtr)){  // won't happen unless foo virtual
    std::cout << "qtr is also pointer to B\n";
  }
  qtr->bar(); // B::bar , polymorphism working




  return 0;
}
