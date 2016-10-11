#include <iostream>

class A {
  public:
  A(const A&){std::cout << "Even if public, compiler won't call me\n";}  // private
  int a;
  public:
  A(int a){this->a = a; std::cout << "A(int) running\n";}
};


int main(){
  A a = 2;
}

