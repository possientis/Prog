#include <memory>
#include <iostream>
// Example of C++ class A for which derivation is disabled.
// use 'sealed' keyword for C#
// use 'final' keyword for Java
// make constructor private. However, you need a way to create instances
// of the class. Hence provide a factory method create()
class A{
  int a;
  A(int a){this->a = a;} // private
  public:
  static std::shared_ptr<A> create(int a){
    std::shared_ptr<A> p(new A(a));
    return p;
  }
  int get(){return a;}
};

class B: public A{
  // B(int a): A(a) {}  // will not compile
};

int main(){

  // B b(100);   // will not compile
  std::shared_ptr<A> p = A::create(100);
  std::cout << p->get() << std::endl;

  return 0;
}
