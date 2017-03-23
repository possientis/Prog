#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

typedef struct { u_int64_t low, high; } u_int128_t;

extern u_int128_t *test_mul_64bits(u_int64_t, u_int64_t, int reg);

int main()
{

  const char* regs[16] = {
    "rax",   "rbx",   "rcx",   "rdx",   "rdi",  "rsi",    "rbp",   "rsp",
    "r8",  "r9",  "r10", "r11", "r12", "r13", "r14", "r15"
  };

  // Native c does not allow us to have integers of more than 64 bits
  // This means we cannot safely multiply numbers together which are 
  // longer than 32 bits as an overflow is most likely to occur.
 
  // The following code attempts to validate the result of multiplying
  // two 64 bits numbers together. The strategy to achieve such validation
  // is to look at the result of such multiplication modulo a chosen prime.
  
  // While we shall be handling many 32 bits quantities, their types are
  // declared as 'u_int64_t' rather than 'u_int32_t' so the compiler 
  // correclty performs 64 bits multiplication thereby avoiding overflow 
  
  u_int64_t p32 = 4000000063UL;     // prime which fits in 32 bits

  // all quantities 'modulo p32' fit in 32 bits and multiplication 
  // can therefore safely occur without overflow.

  // computing 2^64 mod p32. Note that we cannot use '(1UL << 64)'.
  u_int64_t _2_64_mod_p32 = ((1UL << 32) % p32)     // 32 bits
                          * ((1UL << 32) % p32)     // no overflow
                          % p32;                    // 32 bits

  long count = 0, x1, x0, y1, y0;
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

            u_int64_t x64 = x1*4294967296UL + x0;// 64 bits mul 'rax' operand 
            u_int64_t y64 = y1*4294967296UL + y0;// 64 bits mul 'reg' operand 
         

            // obtaing result from assembly instruction 'mul'
            u_int128_t x128 = *test_mul_64bits(x64, y64, i);
         

            u_int64_t x32  = x64 % p32;        // 32 bits 'projection'
            u_int64_t y32  = y64 % p32;        // 32 bits 'projection'

            u_int64_t h32  = x128.high % p32;  // 32 bits proj of high order quad
            u_int64_t l32  = x128.low  % p32;  // 32 bits proj of low order quad

            // Denoting h64 = x128.high and l64 = x128.low, h64 and l64 are
            // respectively the high and low order quad words of the 128 bits
            // quantity returned by the assembly function which is meant to 
            // compute the product of x64 and y64. Hence the equality:
            //
            //   (*) x64 * y64 = h64 * 2^64 + l64
            //
            // We cannot directly validate this equality (unless we use the 
            // C library gmp for infinite precision arithmetic). However, if
            // this equality is true, then the equality obtained by taking
            // both sides modulo p32 should also be true. Hence we expect:
            //
            //  (**) x32 * y32 (mod p32) = h32 * _2_64_mod_p32 + l32 (mod p32)  
            //
            //  (Note that if i = 0, then the assembly function carries out 
            //  a 'mul rax' instruction and returns the square y64 * y64)
            //
            //  This motivates the computation of the following quantities,
            //  each corresponding to one side of equality (**)

            u_int64_t prod1 = (((h32 * _2_64_mod_p32) % p32) + l32) % p32;

            u_int64_t prod2 = (i == 0) ? (y32 * y32) % p32 : (x32 * y32) % p32;

            // we now assert equality (**). This by itself does not prove (*)
            // of course, but it is a meaningful opportunity to disprove it
            // at least. A full test of (*) requires the use of the gmp C library.
            // Note however, that even if we were to check (*) rather than (**),
            // this would not prove correctness of the 'mul' instruction since
            // we can only computationally afford to check correctness on a 
            // limited subspace of all possible operands. 

            assert(prod1 == prod2);
            count++;
          } // y0
        } // y1
      } // x0
    } // x1
  } // i


  printf("\nA total number of %lu checks were performed\n", count);

  return 0;
}
