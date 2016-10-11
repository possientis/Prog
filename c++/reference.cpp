#include <iostream>

class A {
  public:
  virtual void foo(){ std::cout << "A::foo is running\n"; }
};

class B : public A {
  public:
  void foo() override { std::cout << "B::foo is running\n"; }
};

void bar1(A a){
  a.foo();
}

void bar2(A& a){
  a.foo();
}

void bar3(A* a){
  a->foo();
}

A baz1(A& a){
  return a;
}

A& baz2(A& a){
  return a;
}

A* baz3(A& a){
  return &a;
}

int main(){

  A a;
  B b;

  std::cout << "passing arguments by value\n";
  bar1(a);
  bar1(b);  // this compiles, but polymorphism fails A::foo called, not B::foo
  std::cout << "passing arguments by reference\n";
  bar2(a);
  bar2(b);  // polymorphism in action, B::foo called
  std::cout << "passing arguments as pointers\n";
  bar3(&a);
  bar3(&b); // polymorphism in action, B::foo called
  std::cout << "returning object by value\n";
  baz1(a).foo();
  baz1(b).foo();  // polymorphism fails, issue known as 'slicing'?
  std::cout << "returning object by reference\n";
  baz2(a).foo();
  baz2(b).foo();  //  B::foo 
  std::cout << "returning object via pointer\n";
  baz3(a)->foo();
  baz3(b)->foo(); // B::foo

  return 0;
}
