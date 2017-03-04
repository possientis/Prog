// c source code which calls an assembly function
// which itself calls a c function.

#include <stdio.h>
#include <assert.h>

#define LONG(n) 0x##n##n##n##n##n##n##n##n##n##n##n##n##n##n##n##n##UL

// This is the prototype of the assembly function called in this source
// simply returns argument of given index 1-8

unsigned long 
longASMFunction(
    int index, 
    unsigned long x1, 
    unsigned long x2, 
    unsigned long x3, 
    unsigned long x4, 
    unsigned long x5, 
    unsigned long x6, 
    unsigned long x7, 
    unsigned long x8
);

int main()
{
  int i;

  unsigned long x[] = {
    LONG(1),    // 0x1111111111111111L
    LONG(2),    // 0x2222222222222222L
    LONG(3),    // 0x3333333333333333L
    LONG(4),    // 0x4444444444444444L
    LONG(5),    // 0x5555555555555555L
    LONG(6),    // 0x6666666666666666L
    LONG(7),    // 0x7777777777777777L
    LONG(8)     // 0x8888888888888888L
  };

  printf("\nAssembly function call from C with longs ...\n");

  for(i = 0; i < 8; ++i) 
  {
    printf("x%d = 0x%lx\n", i + 1, x[i]);
    
    // checking the call to assembly function is succesful
    // This implicitely validates the call of the assembly 
    // function to the c++ function.

    assert(x[i] == longASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}
