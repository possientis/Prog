/* need to fix this */
#ifndef GET_NUM_H
#define GET_NUM_H
#define GN_NONNEG
#define GN_GT_0
#define GN_ANY_BASE
#define GN_BASE_8
#define GN_BASE_16
01
02
0100
0200
0400
/* Value must be >= 0 */
/* Value must be > 0 */
/*
 */*
     /*
      */*
          By default, integers are decimal */
Can use any base - like strtol(3) */
Value is expressed in octal */
Value is expressed in hexadecimal */
long getLong(const char *arg, int flags, const char *name);
int getInt(const char *arg, int flags, const char *name);
#endif
