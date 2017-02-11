#include <stdio.h>

/* inline assembly forces you to use AT&T syntax */
int getValueFromASM()
{
  asm("movl $253, %eax");
}

/* we avoid inline assembly and write function separately
   on another file, using Intel syntax and yasm */
int getValueFromYASM();

int main()
{

  printf("ASM said %d\n", getValueFromASM());
  printf("YASM said %d\n", getValueFromYASM());

  return 0;
}
