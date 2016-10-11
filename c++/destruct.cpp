#include <iostream>

class A {
  public:
  ~A(){ std::cout << "A::~A() running\n"; }
  A(){ std::cout << "A::A() running\n"; }
  A(A& a){ std::cout << "A::A(A&) running \n"; }
};

class B {
  private: 
    A _a;
  public:
    ~B(){ std::cout << "B::~B running\n"; }
    B(A a): _a(a) { std::cout << "B::B running\n"; }
};






int main(){
  std::cout << "Creating object a\n";
  A a;
  std::cout << "Object a has been created\n";

  std::cout << "Creating object b from a\n";
  B b(a);
  std::cout << "Object b has been created\n";

  std::cout << "Exiting now ...\n";

  return 0;
}
