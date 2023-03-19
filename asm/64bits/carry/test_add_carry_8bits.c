#include <stdint.h>
#include <stdio.h>
#include <assert.h>

// testing the equivalence:
// carry(x,y) = 1 <-> x + y < min(x,y)
extern int add_carry_8bits(uint8_t, uint8_t);

#define MIN(x,y) (((x) < (y)) ? (x) : (y))

int main()
{

  int x, y;

  for(x = 0; x < 256; ++x) {
    for(y = 0; y < 256; ++y) {

      uint8_t x8 = x;
      uint8_t y8 = y;
      uint8_t sum = x8 + y8;
      uint8_t min = MIN(x8,y8);
      int carry = add_carry_8bits(x8,y8);

      assert(carry == (sum < min));

    }
  }

  return 0;
}
