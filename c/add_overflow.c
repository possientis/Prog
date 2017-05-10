#include <assert.h>
#include <stdio.h>

int main()
{
  unsigned int a, b, res;

  signed int sa, sb, sres;

  /* unsigned int */
  a = 0xffffffff; b = 0; res = 0;
  assert(__builtin_uadd_overflow(a,b,&res) == 0); // no carry
  assert(res == 0xffffffff);

  a = 0xffffffff; b = 1; res = 0;
  assert(__builtin_uadd_overflow(a,b,&res) == 1); // carry !!
  assert(res == 0);

  /* signed int */
  sa = 0x7fffffff; sb = 0; sres = 0;
  assert(__builtin_sadd_overflow(sa,sb,&sres) == 0); // no overflow
  assert(sres == 0x7fffffff);


  sa = 0x7fffffff; sb = 1; sres = 0;
  assert(__builtin_sadd_overflow(sa,sb,&sres) == 1); // overflow !!
  assert(sres == -0x80000000);

  return 0;
}
