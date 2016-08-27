//#include<stdio.h>
#include<iostream>  // std::fill, std::cout, std::endl
//#include<vector>
//#include<algorithm>
//#include<iterator>  // std::ostream_iterator<T>
//#include<functional>
//#include <exception>
//#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>

struct Test {

  int field;
  double operator () (double x){
    return 2*x;
  }
};

int foo(double (*)(double)){
  return 23;
}

int main(){

  Test myTest;

  std::cout << myTest(7.6) << std::endl;
  // i would have thought this should work
  //std::cout << foo(myTest) << std::endl;

  return 0;

}
