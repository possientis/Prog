#include <stdint.h>

struct cpu {
  uint64_t rax;
};

extern struct cpu *get_cpu_state();
extern void set_cpu_state(const struct cpu*); 
