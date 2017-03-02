#include <stdio.h>

// summary
// when dealing with binary data, always use 'unsigned char'
// 1. not doing so exposes you to nasty bug (see below)
// 2. Even if your architecture considers char to be unsigned,
// This may not be true on every platform. In fact X86-64 platform
// consider char to be signed, hence 1. is a problem.

int main()
{
  char c1 = 0xff;           // signedness of c1 is platform dependent  
  signed char c2 = 0xff;    // on x86-64, char is 'signed char'
  unsigned char c3 = 0xff;  // on ARM, char is 'unsigned char'


  // c1 is converted to int prior to comparison. On a platform
  // where char is signed, c1 will be signed extended, leading 
  // to a negative integer. The literal 0xff refers to a positive 
  // integer. Hence c1 == 0xff is false.
  // Note bit right shift will not behave the same on signed
  // and unsigned data, another source of bugs ...
  //
  if(c1 == 0xff)
  {
    printf("c1 == 0xff is true\n");
  }
  else
  {
    printf("c1 == 0xff is false\n");
  }

  // same as c1 case on X86-64
  if(c2 == 0xff)
  {
    printf("c2 == 0xff is true\n");
  }
  else
  {
    printf("c2 == 0xff is false\n");
  }

  // This should work as expected.
  if(c3 == 0xff)
  {
    printf("c3 == 0xff is true\n");
  }
  else
  {
    printf("c3 == 0xff is false\n");
  }



}
