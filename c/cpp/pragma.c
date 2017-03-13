// #pragma is a cpp directive, hence cannot be produced as result of macro expansion
// --> _Pragma operator

// touch file parse.y then cpp pragma.c to see the effect of 'GCC dependency' pragma
_Pragma ("GCC dependency \"parse.y\"")    // 1st warning

// same effect as
#pragma GCC dependency "parse.y"          // 2nd warning

#define DO_PRAGMA(x) _Pragma(#x)          // can't do #define DO_PRAGMA(x) #pragma ... 

DO_PRAGMA(GCC dependency "parse.y")       // 3rd warning


#define MY_MACRO 0


#if MY_MACRO
  _Pragma ("GCC dependency \"parse.y\"")  // 4th warning (if MY_MACRO defined and not 0)
#else
  _Pragma("GCC dependency \"parse2.y\"")  // 1st warning (if MY_MACRO undefined or 0)
#endif


#if MY_MACRO
  #pragma GCC dependency "parse.y"        // 5th warning (if ...) 
#else
  #pragma GCC dependency "parse2.y"       // 2nd warning (if ...)
#endif



  


