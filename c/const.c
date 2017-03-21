#include <stdio.h>

int main()
{

  const float pi = 3.14159f;  // read-only

//  pi += 1.0;  // cannot

  int a = 3;
  const int b;

  const int *p = &a;    // pointer to read-only int
//  int*       q = &b;  // compiler warning

  a += 1;               // ok

//  *p += 1;            // not ok 


  int * const q = &a;   // read-only pointer to int

  *q = 5;               // points to writable data

  int c;

//  q = &c;             // pointer is read only         

  int const d = 6;      // 'const int' or 'int const'
//  d = 7;              // cannot

  const int *r = &a;    // pointer to read only int
  int const *s = &a;    // pointer to read only int
  int * const t = &a;    // constant pointer to int


  

  return 0;
}
