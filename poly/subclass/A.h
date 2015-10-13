#ifndef A_INCLUDED
#define A_INCLUDED

#include <iostream>

class A{
  public:
  int a;
  A(int a){this->a = a;}
  virtual void foo(){ std::cout << "A::foo() is running\n";}
};

#endif
