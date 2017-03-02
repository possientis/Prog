#include <stdio.h>
#include <assert.h>

#define CHAR(n) 0x##n##n##U

// simply returns argument of given index 1-8
unsigned char
charASMFunction(
    int index, 
    unsigned char x1, 
    unsigned char x2, 
    unsigned char x3, 
    unsigned char x4, 
    unsigned char x5, 
    unsigned char x6, 
    unsigned char x7, 
    unsigned char x8
);

int main()
{
  int i;

  unsigned char x[] = {
    CHAR(1),     // 0x11U
    CHAR(2),     // 0x22U
    CHAR(3),     // 0x33U
    CHAR(4),     // 0x44U
    CHAR(5),     // 0x55U
    CHAR(6),     // 0x66U
    CHAR(7),     // 0x77U
    CHAR(8)      // 0x88U
  };

  printf("\nAssembly function call from C with chars ...\n");
  for(i = 0; i < 8; ++i) {
    printf("x%d = 0x%02x\n", i + 1, x[i]); 
    assert(x[i] == charASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}
