#include<iostream>

class Base {

  public:
  Base(){std::cout << "running base constructor\n";}
  ~Base(){std:: cout << "running base destructor\n";}
  virtual void foo() {std::cout << "running base foo method\n";}
  void foo(int){std::cout << "running base overloaded foo\n";}

};


class Derived : public Base {

  public:
  Derived(){std::cout << "running derived constructor\n";}
  ~Derived(){std::cout << "running derived destructor\n";}
  void foo(){std::cout << "running derived foo method\n";}
  using Base::foo;
};


int main()
{

  std::cout << "\ncreating base object...\n";
  Base a;
  std::cout << "\ncreating derived object...\n";
  Derived b;
  std::cout << "\ncalling foo on base object...\n";
  a.foo();
  std::cout << "\ncalling overloaded foo on base object...\n";
  a.foo(3);
  std::cout << "\ncalling foo on derived object...\n";
  b.foo();
  std::cout << "\ncalling overloaded base foo on derived object\n";
  b.foo(3);
  std::cout << "\nterminating program...\n";

}
