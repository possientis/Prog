#include <stdint.h>
#include <stdio.h>
#include <assert.h>

extern int64_t test_imul_32bits(int32_t, int32_t, int reg);

static const char* regs[16] = {
    "eax",   "ebx",   "ecx",   "edx",   "edi",  "esi",    "ebp",   "esp",
    "r8d",  "r9d",  "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"
};

 
int main()
{

  int i;
  long x, y;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'imul %s'\n", regs[i]);
    for(x = -2147483648L; x < 2147483648L; x +=902639) {    // partial test
      for(y = -2147483648L; y < 2147483648L; y +=905269) {  // partial test

        // x and y are long which are signed 64 bits integer (on this 
        // platform). However, x and y range from -2^31 to 2^31 - 1 so can
        // fit in 32 bits as unsigned integers. Hence we can cast x and y
        // to int32_t without loss. However, casting x and y to int32_t
        // means the compiler will use 32 bits multiplication when 
        // computing x * y which will overflow. Hence we are casting
        // x and y to 64 bits (signed) integers to force the compiler
        // to carry out 64 bits multiplication, which will not overflow
        // since x and y are 32 bits (signed) integers.
        int64_t x32 = x;
        int64_t y32 = y;

        int64_t z64 = test_imul_32bits(x32,y32,i);
        int64_t t64 = (i == 0) ? y32*y32 : x32*y32;

        assert(z64 == t64);
      }
    }
  }

  return 0;
}
