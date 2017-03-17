#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

struct u_int128_t {
  u_int64_t low;
  u_int64_t high;
};

extern struct u_int128_t *test_mul_64bits(u_int64_t, u_int64_t, int reg);

int main()
{

  const char* regs[16] = {
    "rax",   "rbx",   "rcx",   "rdx",   "rdi",  "rsi",    "rbp",   "rsp",
    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15"
  };

  u_int64_t x64;
  u_int64_t y64;
  u_int64_t x_prev;
  u_int64_t y_prev; 

  int i;

  for(i = 0; i < 16; ++i) {
    printf("checking assembly instruction 'mul %s'\n", regs[i]);
    x64 = 0;
    while(1){
      x_prev = x64;
      x64 = x64 + 0x1122334455667788UL;
      if(x64 < x_prev) break;
    }

  }

  return 0;
}
