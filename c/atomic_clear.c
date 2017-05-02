#include <stdio.h>
#include <assert.h>


int main()
{
  unsigned char byte;

  byte = 0x01;
  __atomic_clear(&byte, __ATOMIC_SEQ_CST);
  assert(byte == 0x00);

  return 0;
}
