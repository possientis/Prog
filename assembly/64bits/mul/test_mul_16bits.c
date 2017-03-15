#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

extern u_int32_t test_mul_16bits(u_int16_t, u_int16_t, int reg);

int main()
{

  const char* regs[16] = {
    "ax",   "bx",   "cx",   "dx",   "di",  "si",    "bp",   "sp",
    "r8w",  "r9w",  "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"
  };

  int x;
  int y;
  int i;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x = 0; x < 65536 ; x +=17) {  // can't test everything
      for(y = 0; y < 65536; y +=23) { // can't test everything

        u_int16_t x16 = (u_int16_t) x;
        u_int16_t y16 = (u_int16_t) y;

        u_int32_t z32 = test_mul_16bits(x16,y16,i);

        if(i == 0) {
          assert( z32 == (u_int32_t) y16*y16);
        }
        else {
          assert( z32 == (u_int32_t) x16*y16);
        }
      }
    }
  }

  return 0;
}
