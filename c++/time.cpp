//#include<stdio.h>
#include <time.h>
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

  std::cout << clock() << std::endl;

  time_t start;
  time_t end;

  time(&start);


  for(long i = 0; i < 10000000; ++i){
    // do nothing
  }

  time(&end);
  std::cout << clock() << std::endl;

  std::cout << start << std::endl;
  std::cout << end << std::endl;




  return 0;

}
