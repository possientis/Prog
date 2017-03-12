#define MY_MACRO

#if defined MY_MACRO
  printf("MY_MACRO is defined\n");
#else
  printf("MY_MACRO is not defined\n");
#endif

#ifdef MY_MACRO
  printf("MY_MACRO is defined\n");
#else
  printf("MY_MACRO is not defined\n");
#endif

#ifndef MY_MACRO
  printf("MY_MACRO is not defined\n");
#else
  printf("MY_MACRO is defined\n");
#endif

// defined is useful for testing several macros
#define MY_OTHER_MACRO

#if defined (MY_MACRO) && defined (MY_OTHER_MACRO)
  printf("both macros are defined\n");
#else
  printf("one of the two macros are not defined\n")
#endif

#define BUFSIZE 2048

#if defined MY_MACRO && BUFSIZE >= 1024
  printf("test was passed\n");
#endif

// if BUZSIZE not defined, will be evaluated as 0
// hence, same as BUFFSIZE >= 1024
#if defined BUFSIZE && BUFSIZE >= 1024
  printf("test was again passed\n");
#endif


#if OTHER_BUFSIZE <= 512  // it is not even defined
  printf("hmmm, are you sure...\n");
#endif










