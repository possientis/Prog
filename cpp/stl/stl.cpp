//#include<stdio.h>
#include<iostream>  // std::fill, std::cout, std::endl
//#include<vector>
//#include<algorithm>
#include<iterator>  // std::ostream_iterator<T>
//#include<functional>
//#include <exception>
//#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>

int main(){

  int array[5];
  int array_2[5] = {2,2,2,2,2};

  std::fill(array,array+5,2);

  for(int i = 0; i < 5; ++i)
    std::cout << "array[" << i << "]=" << array[i] << std::endl;

  std::copy(array,array+5,std::ostream_iterator<int>(std::cout," - "));
  std::cout << std::endl;
  std::copy(array_2,array_2+5,std::ostream_iterator<int>(std::cout," - "));

  if(std::equal(array,array+5,array_2))
    std::cout << "weird things are happening!" << std::endl;
  else
    std::cout << "ok" << std::endl;

  return 0;

}
