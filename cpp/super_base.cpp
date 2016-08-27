#include <iostream>
class A{
  public:
  int a;
  A(int a){this->a = a;}
};

class B : public A{
  public:
  int b;
  B(int a, int b):A(a){this->b = b;}
};

int main(){

  A a(1);
  B b(2,3);

  std::cout << a.a << ":" << b.a << ":" << b.b << std::endl;

  return 0;
}


