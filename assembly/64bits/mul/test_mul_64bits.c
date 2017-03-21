#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

typedef struct {
  u_int64_t low;
  u_int64_t high;
} u_int128_t;

extern u_int128_t *test_mul_64bits(u_int64_t, u_int64_t, int reg);

int main()
{

  const char* regs[16] = {
    "rax",   "rbx",   "rcx",   "rdx",   "rdi",  "rsi",    "rbp",   "rsp",
    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15"
  };

  u_int32_t p = 4000000063UL; // prime which fits in 32 bits
  u_int32_t _264 = ((1UL << 32) % p)*((1UL << 32) %p) % p;

  long x1, x0;
  long y1, y0;
  int i;

  // looping through 64 bits unsigned values with 64 bits unsigned counter
  // will lead to infinite loop. Hence we are using two 64 bits counter to
  // generate a single 64 bits unsigned value.
  for(i = 0; i < 2; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    for(x1 = 0; x1 < 4294967296UL; x1 += 90000083) {
     for(x0 = 0; x0 < 4294967296UL; x0 += 90000083) {
      for(y1 = 0; y1 < 4294967296UL; y1 += 90000083) {
       for(y0 = 0; y0 < 4294967296UL; y0 += 90000083) {
         u_int64_t x64 = x1*4294967296UL + x0;
         u_int64_t y64 = y1*4294967296UL + y0;
         

         u_int128_t x128 = *test_mul_64bits(x64, y64, i);

         u_int32_t x32  = x64 % p;
         u_int32_t y32  = y64 % p;
         u_int32_t h32  = x128.high % p;
         u_int32_t l32  = x128.low  % p;

         u_int64_t prod1 = (((h32 * _264) % p) + l32) % p;
         u_int64_t prod2 = (i == 0) ? (y32 * y32) % p : (x32 * y32) % p;

         if(prod1 != prod2) {
          printf("i = %d\n", i);
          printf("x64 = %lu\n", x64);
          printf("y64 = %lu\n", y64);
          printf("prod1 = %lu\n", prod1);
          printf("prod2 = %lu\n", prod2);
          assert(0);
         }


       }
      }
     }
    }
  }

  return 0;
}
