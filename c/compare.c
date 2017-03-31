#include <stdint.h>
#include <stdio.h>

int main()
{

  uint16_t x; // infinite loop if declared uint8_t
  uint16_t y;

  for(x = 0; x < 256; ++x){
    for(y = 0; y < 256; ++y){
      int8_t a = x;
      int8_t b = y;
      if( x <= y && !(a <= b) ){
        printf("x = %u\ty = %u\ta = %d\tb = %d\n", x, y, a, b);
      }
    }
  }

  return 0;
}
