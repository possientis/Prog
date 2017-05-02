#include <stdio.h>
#include <assert.h>

int main()
{

  unsigned char byte;
  int result;

  /* result = byte; byte = max(1, byte); */
  byte = 0x00;
  result = __atomic_test_and_set(&byte, __ATOMIC_SEQ_CST);
  assert(byte == 0x01); assert(result == 0x00); 

  byte = 0x01;
  result = __atomic_test_and_set(&byte, __ATOMIC_SEQ_CST);
  assert(byte == 0x01); assert(result = 0x01);


  return 0;
}
