#include<iostream>

template<typename T> class Value{
  T data_;
  public:
  // member data_ initialized via copy constructor of T
  Value(T t): data_(t){std::cout << "Value<T> constructor running\n";}
  // member data_ initialized via copy constructor of T
  Value(const Value& rhs):data_(rhs.data_){std::cout << "Value<T> copy constructor running\n";}
  // assignment operator relies on copy constructor and swap
  Value& operator=(Value temp){ // rather than 'const Value &'
    std::cout << "Value<T> assignment operator running\n";
    //Value temp(rhs);  // no need to make copy, passed by value
    swap(temp);
    return *this;
  }
  // destruction of member data_ will require destructor of T
  ~Value(){std::cout << "Value<T> destructor running\n";}
  operator T(){ std::cout << "Value<T> converted to type T\n"; return data_;}
  // initialization of temp requires copy constructor of T
  // data_ = rhs.data_ requires assignment operator of T
  // rhs.data_ = temp requires assignment operator of T
  void swap(Value& rhs){
    std::cout << "Value<T>::swap running\n";
    std::swap(data_,rhs.data_); // don't reinvent the wheel, use std
  }
};

// same code as above but called Box<T> rather than Value<T>
template<typename T> class Box{
  T data_;
  public:
  // member data_ initialized via copy constructor of T
  Box(T t): data_(t){std::cout << "Box<T> constructor running\n";}
  // member data_ initialized via copy constructor of T
  Box(const Box& rhs):data_(rhs.data_){std::cout << "Box<T> copy constructor running\n";}
  // assignment operator relies on copy constructor and swap
  Box& operator=(Box temp){ // rather than 'const Box &'
    std::cout << "Box<T> assignment operator running\n";
    // Box temp(rhs); // no need to make a copy, passed by value
    swap(temp);
    return *this;
  }
  // destruction of member data_ will require destructor of T
  ~Box(){std::cout << "Box<T> destructor running\n";}
  operator T(){ std::cout << "Box<T> converted to type T\n"; return data_;}
  // initialization of temp requires copy constructor of T
  // data_ = rhs.data_ requires assignment operator of T
  // rhs.data_ = temp requires assignment operator of T
  void swap(Box& rhs){
    std::cout << "Box<T>::swap running\n";
    std::swap(data_,rhs.data_); // don't re-invent the wheel use std
  }
};

typedef Value<int> T;

int main(){

  // T = Value<int> so any call to constructor/copy comstructor etc is marked
  // Hence we can check that above comments in code are correct

  T t(5);  // some random value of type T


  // Constructor: we expect copy constructor of T to be called once
  // In fact, things are more complicated:
  // copy constructor of T called once to pass argument t to Box<T> constructor
  // copy constructor of T called a second time to initialize data_ member of Box<T>
  // Then Box<T> constructor's body runs
  // destructor of T is called to destroy temporary T object used to initialize data_
  std::cout << "\n----------- Box<T> constructor -------------------------------\n";
  Box<T> a(t); // Copy/Copy/Destroy
  std::cout << "------------ End Box<T> constructor ---------------------------\n";

  // Copy constructor: we expect copy constructor of T to be called once
  // Unlike what happens in the previous case, the copy constructor of T
  // is not called twice. Argument being passed is a reference and is
  // not of type T anyway (but of type Box<T>).
  std::cout << "\n----------- Box<T> copy constructor --------------------------\n";
  // this is the same as: Box<T> b = a;
  Box<T> b(a);  // Copy
  std::cout << "---------------- End Box<T> copy constructor -------------------\n";


  // Box<T>::swap
  // One copy constructor of T (temporary object built)
  // One assignment operator of T
  // One other assignment operator of T
  // Destructor of T (temporary object destroyed)
  // Note that each call to assignment operator T is itself a call:
  //  - copy / swap / destroy
  std::cout << "\n-------------------- Box<T>::swap ----------------------------\n";
  a.swap(b);  // Copy/Assign/Assign/Destroy
  std::cout << "---------------------- End of Box<T>::swap ---------------------\n";

  // Box<T>::operator=
  // One copy construtor of Box<T>
  // One Box<T>::swap
  // One destructor of Box<T>
  std::cout << "\n------------------ Box<T>::operator= -------------------------\n";
  a = b;  // Copy[Copy]/Swap[Copy/Assign/Assign/Destroy]/Destroy[Destroy]
  std::cout << "-------------------- End of Box<T>::operator= ------------------\n";


  std::cout << "\n---------------- Destructions ----------------------------------\n";
  return 0;
}
