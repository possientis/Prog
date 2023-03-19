#include <stdint.h>
#include <stdio.h>
#include <assert.h>

// testing the equivalence:
// carry(x,y) = (y > x)
extern int sub_carry_8bits(uint8_t, uint8_t);

int main()
{

  int x, y;

  for(x = 0; x < 256; ++x) {
    for(y = 0; y < 256; ++y) {

      uint8_t x8 = x;
      uint8_t y8 = y;
      int carry = sub_carry_8bits(x8,y8);

      assert(carry == (y8 > x8));
    }
  }

  return 0;
}
