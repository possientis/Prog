#include <iostream>
using namespace std;


template <typename T> class Object{

  T* pimpl_;

  public:
  Object():pimpl_(new T()){cout << "default constructor...\n";}
  ~Object(){delete pimpl_; cout << "destructor...\n";}

};


int main(){

  Object<int> a;

}



