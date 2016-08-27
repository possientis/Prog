#include <iostream>
using namespace std;

class Base {

  public:
  Base(){ cout << "Base constructor running...\n";}
  ~Base(){ cout << "Base destructor running...\n";}
  virtual void foo()=0;
};

class A1: public virtual Base {  // keyword 'virtual' here prevents duplication of base object

  public:
  void foo() override { cout << "A1::foo is running...\n";}

};

class A2: public virtual Base {  // keyword 'virtual' here prevents duplication of base object

  public:
  void foo() override { cout << "A2::foo is running...\n";}

};

class B : public A1, public A2 {

  public:
  void foo() override {cout << "B::foo is running...\n";}

};

int main(){

  A1 a1; a1.foo();
  A2 a2; a2.foo();
  B b; b.foo();

  Base *ptr;
  ptr = &a1; ptr->foo();
  ptr = &a2; ptr->foo();
  ptr = &b; ptr->foo();


  return 0;
}
