// c++ source code which calls an assembly function
// which itself calls a c++ function.

#include <iostream>
#include <assert.h>
#include <stdio.h>

using namespace std;

#define CHAR(n) 0x##n##n##U

// This is the prototype of the assembly function called in this source
// simply returns argument of given index 1-8

extern "C" unsigned char
byteASMFunction(
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

  cout << "\nAssembly function call from C++ with chars ...\n";

  for(int i = 0; i < 8; ++i) 
  {
    printf("x%d = 0x%02x\n", i + 1, x[i]); // how do do this with cout? 

    // checking the call to assembly function is succesful
    // This implicitely validates the call of the assembly 
    // function to the c++ function.
    //
    assert(x[i] == byteASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}
