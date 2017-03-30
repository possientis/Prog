#include <stdint.h>
#include <stdio.h>
#include <assert.h>


extern uint16_t test_mul_8bits(uint8_t, uint8_t, int reg);

static const char* regs[16] = {
    "al",   "bl",   "cl",   "dl",   "dil",  "sil",  "bpl",  "spl",
    "r8b",  "r9b",  "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"
};

int main()
{

  int i, x, y;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x = 0; x < 256; ++x) {
      for(y = 0; y < 256; ++y) {

        uint8_t x8 = x;
        uint8_t y8 = y;
        
        uint16_t z16 = test_mul_8bits(x8,y8,i);
        uint16_t t16 = (i == 0) ? y8*y8 : x8*y8;  /* 32 bits mul, no overflow */

        assert(z16 == t16);
      }
    }
  }

  return 0;
}
