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

# ifdef __STDC_VERSION__
  printf("value of __STDC_VERSION__ is: %ld\n", __STDC_VERSION__);
# endif

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

  // Common predefined macros are GNU extensions

  printf("value of __COUNTER__ is: %d\n", __COUNTER__); 
  printf("value of __COUNTER__ is: %d\n", __COUNTER__); 
  printf("value of __COUNTER__ is: %d\n", __COUNTER__); 

# ifdef __GFORTRAN__
 assert(false);
# endif

  printf("value of __GNUC__ is: %d\n", __GNUC__);
  printf("value of __GNUC_MINOR__ is: %d\n", __GNUC_MINOR__);
  printf("value of __GNUC_PATCHLEVEL__ is: %d\n", __GNUC_PATCHLEVEL__);

# define IS_VERSION_EQUAL_OR_ABOVE(_maj,_min,_patch) \
  ((__GNUC__ << 16) + (__GNUC_MINOR__ << 8) + __GNUC_PATCHLEVEL__) >= \
  ((_maj     << 16) + (_min           << 8) + _patch)

# if IS_VERSION_EQUAL_OR_ABOVE(6,3,0)
  printf("gcc version is equal or above 6.3.0\n");
# else
  printf("gcc version is not equal or above 6.3.0\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(6,3,1)
  printf("gcc version is equal or above 6.3.1\n");
# else
  printf("gcc version is not equal or above 6.3.1\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(6,4,0)
  printf("gcc version is equal or above 6.4.0\n");
# else
  printf("gcc version is not equal or above 6.4.0\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(7,3,0)
  printf("gcc version is equal or above 7.3.0\n");
# else
  printf("gcc version is not equal or above 7.3.0\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(6,2,9)
  printf("gcc version is equal or above 6.2.9\n");
# else
  printf("gcc version is not equal or above 6.2.9\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(6,2,0)
  printf("gcc version is equal or above 6.2.0\n");
# else
  printf("gcc version is not equal or above 6.2.0\n");
# endif

# if IS_VERSION_EQUAL_OR_ABOVE(5,15,18)
  printf("gcc version is equal or above 5.15.18\n");
# else
  printf("gcc version is not equal or above 5.15.18\n");
# endif

# ifdef __STRICT_ANSI__
  printf("__STRICT_ANSI__ is defined and equal to %d\n", __STRICT_ANSI__);
# else
  printf("macro __STRICT_ANSI__ is undefined\n");
# endif

  printf("value of __BASE_FILE__ is %s\n", __BASE_FILE__);
  printf("value of __INCLUDE_LEVEL is %d\n", __INCLUDE_LEVEL__);
  printf("value of __ELF__ is %d\n", __ELF__);
  printf("value of __VERSION__ is %s\n", __VERSION__);

# ifdef __OPTIMIZE__
  printf("__OPTIMIZE__ is defined and equal to %d\n", __OPTIMIZE__);
# else
  printf("macro __OPTIMIZE__ is undefined\n");
# endif

# ifdef __OPTIMIZE_SIZE__
  printf("__OPTIMIZE_SIZE__ is defined and equal to %d\n", __OPTIMIZE_SIZE__);
# else
  printf("macro __OPTIMIZE_SIZE__ is undefined\n");
# endif

# ifdef __NO_INLINE__
  printf("__NO_INLINE__ is defined and equal to %d\n", __NO_INLINE__);
# else
  printf("macro __NO_INLINE__ is undefined\n");
# endif

# ifdef __GNUC_GNU_INLINE__
  printf("__GNUC_GNU_INLINE__ is defined and equal to %d\n", __GNUC_GNU_INLINE__);
# else
  printf("macro __GNUC_GNU_INLINE__ is undefined\n");
# endif

# ifdef __GNUC_STDC_INLINE__
  printf("__GNUC_STDC_INLINE__ is defined and equal to %d\n", __GNUC_STDC_INLINE__);
# else
  printf("macro __GNUC_STDC_INLINE__ is undefined\n");
# endif

# ifdef __CHAR_UNSIGNED__
  printf("__CHAR_UNSIGNED__ is defined and equal to %d\n", __CHAR_UNSIGNED__);
# else
  printf("macro __CHAR_UNSIGNED__ is undefined\n");
# endif

# ifdef __WCHAR_UNSIGNED__
  printf("__WCHAR_UNSIGNED__ is defined and equal to %d\n", __WCHAR_UNSIGNED__);
# else
  printf("macro __WCHAR_UNSIGNED__ is undefined\n");
# endif


  printf("value of __CHAR_BIT__ is %d\n", __CHAR_BIT__);
  printf("value of __ORDER_LITTLE_ENDIAN__ is %d\n", __ORDER_LITTLE_ENDIAN__);
  printf("value of __ORDER_BIG_ENDIAN__ is %d\n", __ORDER_BIG_ENDIAN__);
  printf("value of __BYTE_ORDER__ is %d\n", __BYTE_ORDER__);


# ifdef __FLOAT_WORD_ORDER__
  printf("__FLOAT_WORD_ORDER__ is defined and equal to %d\n", __FLOAT_WORD_ORDER__);
# else
  printf("macro __FLOAT_WORD_ORDER__ is undefined\n");
# endif

# ifdef __DEPRECATED
  printf("__DEPRECATED is defined and equal to %d\n", __DEPRECATED);
# else
  printf("macro __DEPRECATED is undefined\n");
# endif

# ifdef __EXCEPTIONS
  printf("__EXCEPTIONS is defined and equal to %d\n", __EXCEPTIONS);
# else
  printf("macro __EXCEPTIONS is undefined\n");
# endif

# ifdef __GXX_RTTI
  printf("__GXX_RTTI is defined and equal to %d\n", __GXX_RTTI);
# else
  printf("macro __GXX_RTTI is undefined\n");
# endif

# ifdef __USING_SJLJ_EXCEPTIONS__
  printf("__USING_SJLJ_EXCEPTIONS__ is defined and equal to %d\n", __USING_SJLJ_EXCEPTIONS__);
# else
  printf("macro __USING_SJLJ_EXCEPTIONS__ is undefined\n");
# endif

# ifdef __GXX_EXPERIMENTAL_CXXOX__
  printf("__GXX_EXPERIMENTAL_CXXOX__ is defined and equal to %d\n", __GXX_EXPERIMENTAL_CXXOX__);
# else
  printf("macro __GXX_EXPERIMENTAL_CXXOX__ is undefined\n");
# endif

# ifdef __GXX_WEAK__
  printf("__GXX_WEAK__ is defined and equal to %d\n", __GXX_WEAK__);
# else
  printf("macro __GXX_WEAK__ is undefined\n");
# endif

# ifdef __NEXT_RUNTIME__
  printf("__NEXT_RUNTIME__ is defined and equal to %d\n", __NEXT_RUNTIME__);
# else
  printf("macro __NEXT_RUNTIME__ is undefined\n");
# endif

# ifdef __LP64__
  printf("__LP64__ is defined and equal to %d\n", __LP64__);
# else
  printf("macro __LP64__ is undefined\n");
# endif

# ifdef _LP64
  printf("_LP64 is defined and equal to %d\n", _LP64);
# else
  printf("macro _LP64 is undefined\n");
# endif

# ifdef __SSP__
  printf("__SSP__ is defined and equal to %d\n", __SSP__);
# else
  printf("macro __SSP__ is undefined\n");
# endif

# ifdef __SSP_ALL__
  printf("__SSP_ALL__ is defined and equal to %d\n", __SSP_ALL__);
# else
  printf("macro __SSP_ALL__ is undefined\n");
# endif

# ifdef __SSP_STRONG__
  printf("__SSP_STRONG__ is defined and equal to %d\n", __SSP_STRONG__);
# else
  printf("macro __SSP_STRONG__ is undefined\n");
# endif

# ifdef __SSP_EXPLICIT__
  printf("__SSP_EXPLICIT__ is defined and equal to %d\n", __SSP_EXPLICIT__);
# else
  printf("macro __SSP_EXPLICIT__ is undefined\n");
# endif

// This does not seem to conform to cpp manual page 31 (34)
# ifdef __SANITIZE_ADDRESS__
  printf("__SANITIZE_ADDRESS__ is defined and equal to %d\n", __SANITIZE_ADDRESS__);
# else
  printf("macro __SANITIZE_ADDRESS__ is undefined\n");
# endif

  printf("current value of __TIMESTAMP__ is %s\n", __TIMESTAMP__);

# ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_1
  printf("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_1 is defined and equal to %d\n", __GCC_HAVE_SYNC_COMPARE_AND_SWAP_1);
# else
  printf("macro __GCC_HAVE_SYNC_COMPARE_AND_SWAP_1 is undefined\n");
# endif

# ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_2
  printf("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_2 is defined and equal to %d\n", __GCC_HAVE_SYNC_COMPARE_AND_SWAP_2);
# else
  printf("macro __GCC_HAVE_SYNC_COMPARE_AND_SWAP_2 is undefined\n");
# endif

# ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_4
  printf("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4 is defined and equal to %d\n", __GCC_HAVE_SYNC_COMPARE_AND_SWAP_4);
# else
  printf("macro __GCC_HAVE_SYNC_COMPARE_AND_SWAP_4 is undefined\n");
# endif

# ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_8
  printf("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_8 is defined and equal to %d\n", __GCC_HAVE_SYNC_COMPARE_AND_SWAP_8);
# else
  printf("macro __GCC_HAVE_SYNC_COMPARE_AND_SWAP_8 is undefined\n");
# endif

# ifdef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_16
  printf("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_16 is defined and equal to %d\n", __GCC_HAVE_SYNC_COMPARE_AND_SWAP_16);
# else
  printf("macro __GCC_HAVE_SYNC_COMPARE_AND_SWAP_16 is undefined\n");
# endif

# ifdef __GCC_HAVE_DWARF2_CFI_ASM
  printf("__GCC_HAVE_DWARF2_CFI_ASM is defined and equal to %d\n", __GCC_HAVE_DWARF2_CFI_ASM);
# else
  printf("macro __GCC_HAVE_DWARF2_CFI_ASM is undefined\n");
# endif


# ifdef __FP_FAST_FMA
  printf("__FP_FAST_FMA is defined and equal to %d\n", __FP_FAST_FMA);
# else
  printf("macro __FP_FAST_FMA is undefined\n");
# endif

# ifdef __FP_FAST_FMAF
  printf("__FP_FAST_FMAF is defined and equal to %d\n", __FP_FAST_FMAF);
# else
  printf("macro __FP_FAST_FMAF is undefined\n");
# endif

# ifdef __FP_FAST_FMAL
  printf("__FP_FAST_FMAL is defined and equal to %d\n", __FP_FAST_FMAL);
# else
  printf("macro __FP_FAST_FMAL is undefined\n");
# endif

# ifdef __NO_MATH_ERRNO__
  printf("__NO_MATH_ERRNO__ is defined and equal to %d\n", __NO_MATH_ERRNO__);
# else
  printf("macro __NO_MATH_ERRNO__ is undefined\n");
# endif

  /***************************************************************************/
  /*                 SYSTEM-SPECIFIC PREDEFINED MACROS                       */
  /***************************************************************************/




  return 0;
}


void func(void)
{
  printf("current function is: %s\n", __func__);      // C99 standard
  printf("current function is: %s\n", __FUNCTION__);  // GNU
}


