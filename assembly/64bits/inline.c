#include <stdio.h>

/* possible to use 'gcc -masm=intel ...' and replace
 * at&t syntax with intel syntax in asm statements */


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
