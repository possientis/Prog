#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

extern u_int16_t test_mul_8bits(u_int8_t, u_int8_t, int reg);

int main()
{

  const char* regs[16] = {
    "al",   "bl",   "cl",   "dl",   "dil",  "sil",  "bpl",  "spl",
    "r8b",  "r9b",  "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"
  };

  int x;
  int y;
  int i;

  for(i = 0; i < 5; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x = 0; x < 256; ++x) {
      for(y = 0; y < 256; ++y) {

        u_int8_t x8 = (u_int8_t) x;
        u_int8_t y8 = (u_int8_t) y;

        u_int16_t z16 = test_mul_8bits(x8,y8,i);

        if(i == 0) {
          assert( z16 == (u_int16_t) y8*y8);
        }
        else {
          assert( z16 == (u_int16_t) x8*y8);
        }
      }
    }
  }

  return 0;
}
