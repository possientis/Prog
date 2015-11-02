#include <iostream>


template <typename T> class IPointer {
  public:
    virtual ~IPointer(){}
    virtual T& operator*() const = 0;
    virtual T* operator->() const = 0;
}; 

template <typename T> class Pointer : public IPointer<T> {

  T* _pointer;
  int* _count;

  public:
    ~Pointer(){(*_count)--; if(*_count == 0){delete _pointer; delete _count;}}
    Pointer(T* p):_pointer(p),_count(new int(1)){}
    int count() const {return *_count;}
    T& operator*() const override {return *(_pointer);}
    T* operator->() const override{return _pointer;}
};

class K{
  int a;
  public:
  K(int a){this->a = a;}
  void foo(){std::cout << "K::foo() is running\n";}
  int get(){return a;}
};

typedef Pointer<K> A;


int main(){

  A a(new K(100));

  std::cout << a.count() << std::endl;
  std::cout << (*a).get() << std::endl;
  std::cout << a->get() << std::endl;
  a->foo();

  return 0;

}
