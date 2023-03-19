#include <stdio.h>
#include <stdint.h>

/* Extended asm syntax
 * asm [volatile] ( AssemblerTemplate
 * : OutputOperands
 * [ : InputOperands
 * [ : Clobbers ] ])
 *
 * asm [volatile] goto ( AssemblerTemplate
 * :
 * : InputOperands
 * : Clobbers
 * : GotoLabels)
 *
 */

// compile with -masm=intel option if using intel syntax
// gcc -masm=intel -DINTEL=1 asm.c
//#define INTEL


#ifndef INTEL
# define CODE "mov %1, %0\n\tadd $1, %0"  // at&t syntax
#else
# define CODE "mov %0, %1\n\t add %0, 1"  // intel syntax
#endif

int main()
{
  

  int src = 1;
  int dst;

  asm(CODE : "=r" (dst) : "r" (src));
  printf("dst = %d\n", dst);

#ifndef INTEL

  asm("mov %[aSrc], %[aDst]""\n\t"
      "add $2, %[aDst]"
      : [aDst] "=r" (dst)
      : [aSrc] "r"  (src)
      : "cc");
  printf("dst = %d\n", dst);
#endif


#ifndef INTEL
  // can't say I really understand this
  uint64_t msr;
  asm volatile (  "rdtsc\n\t"           // returns the time in EDX:EAX
                  "shl $32, %%rdx\n\t"  // shift the upper bits left 
                  "or %%rdx, %0"        // 'or' in the lower bits
                  : "=a" (msr)
                  :                     // no input
                  : "rdx");             // telling which values changed.

  printf("msr:%llx\n", msr);
#endif

  return 0;
}
