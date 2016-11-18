#include <stdio.h>
#include <stdint.h>


int main()
{
  // semantics of right shift operator >> differs depending
  // on whether integer is signed or unsigned

  printf("(uint16_t) -1 >> 15 = %d\n", (uint16_t) -1 >> 15);  // 1
  printf("(int16_t)  -1 >> 15 = %d\n", (int16_t)  -1 >> 15);  // -1

  return 0;
}
