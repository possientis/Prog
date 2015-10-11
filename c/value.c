#include<iostream>
using namespace std;

template<typename T> class Value{
  T data_;
  public:
  Value(T t): data_(t){cout << "Value constructor running\n";}
  Value(const Value& rhs):data_(rhs.data_){cout << "Value copy constructor running\n";}
  Value& operator=(const Value&);
  ~Value(){cout << "Value destructor running\n";}
  operator T(){return data_;}
  private:
  void swap(Value& rhs){T temp = data_; data_ = rhs.data_; rhs.data_ = temp;}
};

template <typename T>
Value<T>& Value<T>::operator=(const Value& rhs){
  cout << "Value assignment operator running\n";
  Value temp(rhs); swap(temp);
  return *this;
}

template<typename T> class Box{
  int count_;
  T data_;
  public:
  Box(T t) : count_(0), data_(t){cout << "Box constructor running\n";}
  Box(const Box& rhs);
  Box& operator=(const Box& rhs);
  ~Box(){cout << "Box destructor running \n";};
  private:
  void swap(Box& rhs);
};




typedef Value<int> A;
typedef Box<A> B;

int main(){

  B a(3);
  cout << "first object built\n";
  B b(5);
  cout << "second object built\n";

  cout << "size = " << sizeof(a) << endl;

  return 0;
}
