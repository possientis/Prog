// Pointer.h
#ifndef POINTER_INCLUDED
#define POINTER_INCLUDED

#include <utility> // std::swap

template <typename T> class IPointer {
  public:
    virtual ~IPointer(){}
    virtual T& operator*() const = 0;
    virtual T* operator->() const = 0;
}; 


template <typename T> class Pointer : public IPointer<T> {

  T* _pointer;
  int* _count;
  void swap(Pointer<T> p){  // private no fail swap for assignment operator
    std::swap<T*>(_pointer,p._pointer); 
    std::swap<int*>(_count,p._count);
  }

  public:
    ~Pointer(){(*_count)--; if(*_count == 0){delete _pointer; delete _count;}}
    Pointer(T* p) :_pointer(p),_count(new int(1)){}
    Pointer(const Pointer<T>& p):_pointer(p._pointer),_count(p._count){
      (*_count)++;
    }
    Pointer<T>& operator=(const Pointer<T>& rhs){
      Pointer<T> temp(rhs);
      swap(temp);
    }
    int count() const {return *_count;}
    T* get() const {return _pointer;}
    T& operator*() const override {return *(_pointer);}
    T* operator->() const override{return _pointer;}
};

#endif

