// Three categories of predefined macros: standard, common, system-specific
// c++ offers a fourth category: named operators

#include <stdio.h>
#include <assert.h>
#include <string.h>

void func(void);

int main()
{
  /***************************************************************************/
  /*                   STANDARD PREDEFINED MACROS                            */
  /***************************************************************************/

  // useful for error messages
  printf("current input file is: %s\n", __FILE__);        
  printf("current source code line is: %d\n", __LINE__);  
  func(); // __func__ and __FUNCTION__
  
  // date when cpp is run, not when program is running, duh !
  printf("current date is: %s\n", __DATE__);
  assert(strlen(__DATE__) == 11); // always the case

  // time when cpp is run, not when program is running, duh !
  printf("current time is: %s\n", __TIME__);
  assert(strlen(__TIME__) == 8); // always the case

  // should always be 1 with GNU cpp and gcc
  printf("value of __STDC__ is: %d\n", __STDC__);
  assert(__STDC__ == 1);

  printf("value of __STDC_VERSION__ is: %ld\n", __STDC_VERSION__);

  // should be 1 if compiler target is hosted environment, i.e.
  // where complete facilities of the standard c library available.
  printf("value of __STDC_HOSTED__ is: %d\n", __STDC_HOSTED__);
  assert(__STDC_HOSTED__ == 1);

  // __cplusplus defined when c++ compiler is in use, in which case
  // value is some long version number similar to __STDC_VERSION__
# ifdef cplusplus
  assert(false);
# endif

  // __OBJC__ defined with value 1 when objective c compiler in use.
# ifdef __OBJC__
  assert(false);
# endif

  // __ASSEMBLER__ defined with value 1 when preprocessing assembly language
# ifdef __ASSEMBLER__
  assert(false);
# endif

  /***************************************************************************/
  /*                     COMMON PREDEFINED MACROS                            */
  /***************************************************************************/

  return 0;
}


void func(void)
{
  printf("current function is: %s\n", __func__);      // C99 standard
  printf("current function is: %s\n", __FUNCTION__);  // GNU
}


