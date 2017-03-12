// #pragma is a cpp directive, hence cannot be produced as result of macro expansion
// --> _Pragma operator

_Pragma ("GCC dependency \"parse.y\"")

// same effect as
#pragma GCC dependency "parse.y"

#define DO_PRAGMA(x) _Pragma(#x)

DO_PRAGMA(GCC dependency "parse.y")


