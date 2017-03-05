#include <stdio.h>
#include <stdlib.h>


unsigned short
wordFunction(
    int index,
    unsigned short x1, 
    unsigned short x2, 
    unsigned short x3, 
    unsigned short x4, 
    unsigned short x5, 
    unsigned short x6, 
    unsigned short x7, 
    unsigned short x8
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
      fprintf(stderr, "wordFunction: invalid index argument\n");
      exit(1);
  }
}
        
            
