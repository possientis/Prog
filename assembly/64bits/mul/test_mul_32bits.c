#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

extern u_int64_t test_mul_32bits(u_int32_t, u_int32_t, int reg);

int main()
{

  const char* regs[16] = {
    "eax",   "ebx",   "ecx",   "edx",   "edi",  "esi",    "ebp",   "esp",
    "r8d",  "r9d",  "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"
  };

  long x;
  long y;
  int i;

  for(i = 0; i < 2; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x = 0; x < 4294967296UL ; x +=902639) {  // can't test everything
      for(y = 0; y < 4294967296UL; y +=905269) { // can't test everything

        u_int32_t x32 = (u_int32_t) x;
        u_int32_t y32 = (u_int32_t) y;

        u_int64_t z64 = test_mul_32bits(x32,y32,i);

        if(i == 0) {
          assert( z64 == (u_int64_t) y32*y32);
        }
        else {
          assert( z64 == (u_int64_t) x32*y32);
        }
      }
    }
  }

  return 0;
}
