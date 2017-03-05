#include <iostream>
#include <stdlib.h>

using namespace std;

extern "C" unsigned short 
byteFunction(
    int index,
    unsigned char x1, 
    unsigned char x2, 
    unsigned char x3, 
    unsigned char x4, 
    unsigned char x5, 
    unsigned char x6, 
    unsigned char x7, 
    unsigned char x8
)
{
  switch(index)
  {
    case 1: return x1;
    case 2: return x2;
    case 3: return x3;
    case 4: return x4;
    case 5: return x5;
    case 6: return x6;
    case 7: return x7;
    case 8: return x8;
    default: 
      cerr << "byteFunction: invalid index argument\n";
      exit(1);
  }
}           


