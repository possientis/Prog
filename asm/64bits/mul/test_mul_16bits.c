#include <stdint.h>
#include <stdio.h>
#include <assert.h>

extern uint32_t test_mul_16bits(uint16_t, uint16_t, int reg);

static const char* regs[16] = {
    "ax",   "bx",   "cx",   "dx",   "di",  "si",    "bp",   "sp",
    "r8w",  "r9w",  "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"
};


int main()
{

  int i, x, y;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x = 0; x < 65536 ; x +=53) {  // can't test everything
      for(y = 0; y < 65536; y +=53) { // can't test everything

        uint16_t x16 = x;
        uint16_t y16 = y;

        uint32_t z32 = test_mul_16bits(x16,y16,i);
        uint32_t t32 = (i == 0) ? y16*y16 : x16*y16; /* 32 bits mul, no overflow */

        assert(z32 == t32);
      }
    }
  }

  return 0;
}
