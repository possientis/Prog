#include<stdio.h>
//#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>




int main()
{

  int x = 5;
  int y = 5;

  int z = x + (x=0);
  int t = (y=0) + y;

  printf("starting from x = 5\n");
  printf("x + (x=0) evaluates to: %d\n",z);
  printf("(x=0) + x evaluates to: %d\n",t);


  return 0;


}

