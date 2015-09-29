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


int main(){

  int *x = new int(3);

  std::cout << *x << std::endl;

  delete(x);

  return 0;

}
