#include<stdio.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>

struct Int1 {
  int data;
};

typedef int Int2;

void f1(int);
void f2(Int1);
void f3(Int2);

int main()
{

  Int2 n;

  f1(n);
  //f2(n);
  f3(n);

  return 0;


}

void f1(int n){printf("f1 running\n");}
void f2(Int1 n){printf("f2 running\n");}
void f3(Int2 n){printf("f3 running\n");}
