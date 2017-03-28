#include <stdio.h>
#include <stdint.h>

int main()
{
  uint8_t x8 = 0xff;
  printf("\nuint8_t x8 = %llx\n", x8);
  printf("x8 << 1 = %llx\n", (x8 << 1));
  printf("x8 >> 1 = %llx\n", (x8 >> 1));
  printf("sizeof(x8) = %d\n", sizeof(x8));

  uint16_t x16 = 0xffff;
  printf("\nuint16_t x16 = %llx\n", x16);
  printf("x16 << 1 = %llx\n", (x16 << 1));
  printf("x16 >> 1 = %llx\n", (x16 >> 1));
  printf("sizeof(x16) = %d\n", sizeof(x16));


  uint32_t x32 = 0xffffffff;
  printf("\nuint32_t x32 = %llx\n", x32);
  printf("x32 << 1 = %llx (no '1' to the left !!)\n", (x32 << 1));
  printf("x32 >> 1 = %llx\n", (x32 >> 1));
  printf("sizeof(x32) = %d\n", sizeof(x32));

  uint64_t x64 = 0xffffffffffffffffUL;
  printf("\nuint64_t x64 = %llx\n", x64);
  printf("x64 << 1 = %llx (no '1' to the left !!)\n", (x64 << 1));
  printf("x64 >> 1 = %llx\n", (x64 >> 1));
  printf("sizeof(x64) = %d\n", sizeof(x64));

  int8_t  y8  = -1;
  printf("\nint8_t y8 = %llx\n", y8);
  printf("y8 << 1 = %llx\n", (y8 << 1));
  printf("y8 >> 1 = %llx\n", (y8 >> 1));
  printf("sizeof(y8) = %d\n", sizeof(y8));

  int16_t  y16  = -1;
  printf("\nint16_t y16 = %llx\n", y16);
  printf("y16 << 1 = %llx\n", (y16 << 1));
  printf("y16 >> 1 = %llx\n", (y16 >> 1));
  printf("sizeof(y16) = %d\n", sizeof(y16));

  int32_t  y32  = -1;
  printf("\nint32_t y32 = %llx\n", y32);
  printf("y32 << 1 = %llx\n", (y32 << 1));
  printf("y32 >> 1 = %llx\n", (y32 >> 1));
  printf("sizeof(y32) = %d\n", sizeof(y32));

  int64_t  y64  = -1;
  printf("\nint64_t y64 = %llx\n", y64);
  printf("y64 << 1 = %llx\n", (y64 << 1));
  printf("y64 >> 1 = %llx\n", (y64 >> 1));
  printf("sizeof(y64) = %d\n", sizeof(y64));

  return 0;
}
