#include <iostream>

class A {
  public:
    A(){ std::cout << "allocating new object\n"; }
    ~A(){ std::cout << "deallocating existing object\n"; }
    A& foo(){ return *this; }
};


int main(){
  A a;
  // when b goes out of scope, destructor is not called on object
  // referred to by b. 
  A& b = a.foo();

  return 0;
}
