#include<iostream>

class Base {

  public:
   Base(){std::cout << "running base constructor\n";}
  ~Base(){std:: cout << "running base destructor\n";}
  virtual void foo() {std::cout << "running base foo method\n";}
  void bar(){std::cout << "running base bar method\n";} // forgetting to declare virtual
};


class Derived : public Base {

  public:
  Derived(){std::cout << "running derived constructor\n";}
  ~Derived(){std::cout << "running derived destructor\n";}
  void foo(){std::cout << "running derived foo method\n";}  // overriding virtual method
  void bar(){std::cout << "running derived bar method\n";}  // hiding base method
};


int main()
{

  std::cout << "\ncreating base object...\n";
  Base a;
  std::cout << "\ncreating derived object...\n";
  Derived b;
  std::cout << "\ncalling foo on base object...\n";
  a.foo();
  std::cout << "\ncalling foo on derived object...\n";
  b.foo();
  std::cout << "\ndefining base pointer, pointing to derived object..\n";
  Base *ptr = &b;
  std::cout << "\ncalling foo on pointer...\n";
  ptr->foo();
  std::cout << "\ncalling bar on pointer...(watch out for error)\n";
  ptr->bar();   // error, base 'bar' is called, not derived
  std::cout << "\nterminating program...\n";


}
