# include <sys/types.h>
# include <stdio.h>

struct test {
  unsigned int field1:4;
  unsigned int field2:4;
} __attribute__((packed));

int main()
{

  printf("size of struct test = %d\n", sizeof(struct test));

  struct test a;

  a.field1 = 0x1;
  a.field2 = 0x2;

  u_int8_t *b;

  b = (u_int8_t *) &a;

  printf("a = %x\n", *b);


  return 0;
}
