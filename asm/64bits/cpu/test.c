#include <stdint.h>
#include <stdio.h>

#include "cpu.h"


int main()
{
  struct cpu x;
  struct cpu *p;

  x.rax = 0x1122334455667788UL;
  set_cpu_state(&x);

  p = get_cpu_state();

  uint64_t rax = p->rax;
  printf("rax = %lx\n", rax);

   
  return 0;
}
