#include<stdio.h>
//#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>




int main()
{

  int x = 5;
  int &y = x;


  printf("x = %d\n",x);
  printf("y = %d\n",y);

  x = 6;
  printf("y = %d\n",y);


  return 0;


}

