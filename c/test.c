#include<stdio.h>
//#include<assert.h>
//#include<assert.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>

int *ap;
int a[5]={41,42,43,44,45};
int x;

int main()
{
  ap = a[4];
  x = *ap;
  printf("%d",x);
  return 0;
}


