#include<stdio.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>

int foo(const char* control, ...){

  printf("%s\n",control);

  return 0;

}

int main()
{

//  using namespace std;

  foo("hi", "hello", "here");

  return 0;


}


