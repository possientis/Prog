#include <stdint.h>
#include <stdio.h>
#include <assert.h>

extern int32_t test_imul_16bits(int16_t, int16_t, int reg);

static const char* regs[16] = {
    "ax",   "bx",   "cx",   "dx",   "di",  "si",    "bp",   "sp",
    "r8w",  "r9w",  "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"
};


int main()
{

  int i, x, y;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'imul %s'\n", regs[i]);
    for(x = -32768; x < 32768 ; x +=53) {  // can't test everything
      for(y = -32768; y < 32768; y +=53) { // can't test everything

        int16_t x16 = x;
        int16_t y16 = y;

        int32_t z32 = test_imul_16bits(x16,y16,i);
        int32_t t32 = (i == 0) ? y16*y16 : x16*y16; /* 32 bits mul, no overflow */
        if(z32 != t32){
          printf("i = %d\n", i);
          printf("x = %d\n", x);
          printf("y = %d\n", y);
          printf("x16 = %d\n", x16);
          printf("y16 = %d\n", y16);
          printf("z32 (asm call) = %d\n", z32);
          printf("t32 (c call)   = %d\n", t32);
        }
        assert(z32 == t32);
      }
    }
  }

  return 0;
}
