#include<stdio.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>

typedef int (Func)(int x);
typedef int (*Gunc)(int x);


int f(int x){

  return 2*x;

}

int main()
{

  Func *g;

  g = &f;

  int x = (&f)(3);

  printf("%d\n",x);
  return 0;


}

