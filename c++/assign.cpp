#include<iostream>

class A{

  public:
  A& operator=(A&){std::cout << "operator= running\n";} // argument is not const
  A(){}



};


int main(){

  A a;
  A b;

  a = b;  // assignment ok

  // a = A(); // does not compile, should be operator=(const A&)

  return 0;

}
