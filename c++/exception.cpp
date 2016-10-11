#include<stdio.h>
#include <exception>
//#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>



void f() throw(std::exception){

  printf("function f is running...\n");

      throw std::exception();
//    throw 20;

}


int main()
{
  try
  {
    f();
  }
  catch(const std::exception& e)
  {
    printf("Exception is caught:%s\n",e.what());
  }
  catch(int)
  {
    printf("int Exception is caught\n");
  }

  return 0;

}

