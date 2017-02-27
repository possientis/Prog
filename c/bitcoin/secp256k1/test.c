//#define SECP256K1_BUILD
#include "secp256k1/include/secp256k1.h"


#include <assert.h>
#include <stdio.h>

/* trick to convert value of a macro into a string constant */
# define STR(EXP) "\'"STR_(EXP)"\'" 
# define STR_(EXP) #EXP /* # is preprocesssor 'stringify operator' */

int main()
{
  secp256k1_context *ctx;         // pointer
  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(ctx) == 8);
  assert(sizeof(pub) == 64);
  assert(sizeof(sig) == 64);
  assert(sizeof(fun) == 8);

# if defined(SECP256K1_GNUC_PREREQ)
  printf("SECP256K1_GNUC_PREREQ is defined\n");
  printf("SECP256K1_GNUC_PREREQ(6,1)=%d\n", SECP256K1_GNUC_PREREQ(6,1));
  printf("SECP256K1_GNUC_PREREQ(6,2)=%d\n", SECP256K1_GNUC_PREREQ(6,2));
  printf("SECP256K1_GNUC_PREREQ(6,3)=%d\n", SECP256K1_GNUC_PREREQ(6,3));
  printf("SECP256K1_GNUC_PREREQ(5,2)=%d\n", SECP256K1_GNUC_PREREQ(5,2));
  printf("SECP256K1_GNUC_PREREQ(7,2)=%d\n", SECP256K1_GNUC_PREREQ(7,2));
# else
  printf("SECP256K1_GNUC_PREREQ is not defined\n");
# endif

# if defined(__GNUC__)
  printf("__GNUC__ is defined and equal to %d\n", __GNUC__);
# else
  printf("__GNUC__is not defined\n");
# endif
 
# if defined(__GNUC_MINOR__)
  printf("__GNUC_MINOR__ is defined and equal to %d\n", __GNUC_MINOR__);
# else
  printf("__GNUC_MINOR__ is not defined\n");
# endif 


# if defined(__STDC_VERSION__)
  printf("__STDC_VERSION__ is defined and equal to %d\n", __STDC_VERSION__);
# else
  printf("__STDC_VERSION__ is not defined\n");
# endif

# if defined(SECP256K1_INLINE)
  printf("SECP256K1_INLINE is defined and equal to %s\n", STR(SECP256K1_INLINE));
# else
  printf("SECP256K1_INLINE is not defined\n");
# endif


# if defined(_WIN32)
  printf("_WIN32 is defined and equal to %s\n", STR(_WIN32));
# else
  printf("_WIN32 is not defined\n");
# endif

# if defined(SECP256K1_BUILD)
  printf("SECP256K1_BUILD is defined and equal to %s\n", STR(SECP256K1_BUILD));
# else
  printf("SECP256K1_BUILD is not defined\n");
# endif


# if defined(SECP256K1_API)
  printf("SECP256K1_API is defined and equal to %s\n", STR(SECP256K1_API));
# else
  printf("SECP256K1_API is not defined\n");
# endif


# if defined(SECP256K1_WARN_UNUSED_RESULT)
  printf("SECP256K1_WARN_UNUSED_RESULT is defined and equal to %s\n", 
      STR(SECP256K1_WARN_UNUSED_RESULT));
# else
  printf("SECP256K1_WARN_UNUSED_RESULT is not defined\n");
# endif


# if defined(SECP256K1_ARG_NONNULL)
  printf("SECP256K1_ARG_NONNULL is defined\n");
  printf("SECP2561K1_ARG_NONNULL(x) = %s\n", STR(SECP256K1_ARG_NONNULL(x)));
# else
  printf("SECP256K1_ARG_NONULL is not defined\n");
# endif


# if defined(SECP256K1_FLAGS_TYPE_MASK)
  printf("SECP256K1_FLAGS_TYPE_MASK is defined and equal to %d\n", 
      SECP256K1_FLAGS_TYPE_MASK);
# else
  printf("SECP256K1_FLAGS_TYPE_MASK is not defined\n");
# endif

# if defined(SECP256K1_FLAGS_TYPE_CONTEXT)
  printf("SECP256K1_FLAGS_TYPE_CONTEXT is defined and equal to %d\n", 
      SECP256K1_FLAGS_TYPE_CONTEXT);
# else
  printf("SECP256K1_FLAGS_TYPE_CONTEXT is not defined\n");
# endif

# if defined(SECP256K1_FLAGS_TYPE_COMPRESSION)
  printf("SECP256K1_FLAGS_TYPE_COMPRESSION is defined and equal to %d\n", 
      SECP256K1_FLAGS_TYPE_COMPRESSION);
# else
  printf("SECP256K1_FLAGS_TYPE_COMPRESSION is not defined\n");
# endif

# if defined(SECP256K1_FLAGS_BIT_CONTEXT_VERIFY)
  printf("SECP256K1_FLAGS_BIT_CONTEXT_VERIFY is defined and equal to %d\n", 
      SECP256K1_FLAGS_BIT_CONTEXT_VERIFY);
# else
  printf("SECP256K1_FLAGS_BIT_CONTEXT_VERIFY is not defined\n");
# endif

# if defined(SECP256K1_FLAGS_BIT_CONTEXT_SIGN)
  printf("SECP256K1_FLAGS_BIT_CONTEXT_SIGN is defined and equal to %d\n", 
      SECP256K1_FLAGS_BIT_CONTEXT_SIGN);
# else
  printf("SECP256K1_FLAGS_BIT_CONTEXT_SIGN is not defined\n");
# endif

# if defined(SECP256K1_FLAGS_BIT_COMPRESSION)
  printf("SECP256K1_FLAGS_BIT_COMPRESSION is defined and equal to %d\n", 
      SECP256K1_FLAGS_BIT_COMPRESSION);
# else
  printf("SECP256K1_FLAGS_BIT_COMPRESSION is not defined\n");
# endif


# if defined(SECP256K1_CONTEXT_VERIFY)
  printf("SECP256K1_CONTEXT_VERIFY is defined and equal to %d\n", 
      SECP256K1_CONTEXT_VERIFY);
# else
  printf("SECP256K1_CONTEXT_VERIFY is not defined\n");
# endif

# if defined(SECP256K1_CONTEXT_SIGN)
  printf("SECP256K1_CONTEXT_SIGN is defined and equal to %d\n", 
      SECP256K1_CONTEXT_SIGN);
# else
  printf("SECP256K1_CONTEXT_SIGN is not defined\n");
# endif

# if defined(SECP256K1_CONTEXT_NONE)
  printf("SECP256K1_CONTEXT_NONE is defined and equal to %d\n", 
      SECP256K1_CONTEXT_NONE);
# else
  printf("SECP256K1_CONTEXT_NONE is not defined\n");
# endif

# if defined(SECP256K1_EC_COMPRESSED)
  printf("SECP256K1_EC_COMPRESSED is defined and equal to %d\n", 
      SECP256K1_EC_COMPRESSED);
# else
  printf("SECP256K1_EC_COMPRESSED is not defined\n");
# endif

# if defined(SECP256K1_EC_UNCOMPRESSED)
  printf("SECP256K1_EC_UNCOMPRESSED is defined and equal to %d\n", 
      SECP256K1_EC_UNCOMPRESSED);
# else
  printf("SECP256K1_EC_UNCOMPRESSED is not defined\n");
# endif














  return 0;
}
