#include<stdio.h>
// typeof is a gnu extension


void int_foo(int a){
  printf("int_foo is running\n");
}

void double_foo(double a){
  printf("double_foo is running\n");
}

// can we emulate overloading with 'typeof'

int main()
{

  int x = 5;
  double y = 3.0;

  return 0;
}

