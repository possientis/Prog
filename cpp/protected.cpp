#include <iostream>

class A {
  protected: 
    A* a;
  public:
    A() : a(nullptr) {}
    A(A* ptr) : a(ptr) {}
};

class B : A {
  public:
  B(A* ptr): A(ptr) {}
  void foo();
};


void B::foo(){
  // member a of base object being protected, it is accessible with
  // code of derived object
  if(a == nullptr){
    std::cout << "my pointer is null\n";
  } else {
    std::cout << "my pointer is not null";
  }

  // we are in code of derived class, but we are attempting to 
  // access protected member which is not the derived object.

  // fail to compile
  /* 
  if(a->a == nullptr){
    std::cout << "The pointer of my pointer is null\n";
  } else {
    std::cout << "The pointer of my pointer is not null\n";
  }
  */
}




int main(){

  A a;

  B b(&a);

  b.foo();



  return 0;
}
