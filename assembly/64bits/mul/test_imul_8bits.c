#include <stdint.h>
#include <stdio.h>
#include <assert.h>


extern int16_t test_imul_8bits(int8_t, int8_t, int reg);

static const char* regs[16] = {
    "al",   "bl",   "cl",   "dl",   "dil",  "sil",  "bpl",  "spl",
    "r8b",  "r9b",  "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"
};

int main()
{

  int i, x, y;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'imul %s'\n", regs[i]);
    for(x = -128; x < 128; ++x) {
      for(y = -128; y < 128; ++y) {

        int8_t x8 = x;
        int8_t y8 = y;
        
        int16_t z16 = test_imul_8bits(x8,y8,i);
        int16_t t16 = (i == 0) ? y8*y8 : x8*y8;  /* 32 bits mul, no overflow */

        assert(z16 == t16);
      }
    }
  }

  return 0;
}
