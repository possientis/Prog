#include "secp256k1.h"
#include <stdio.h>


int main(){

  printf("Symbol value =%d\n", SECP256K1_EC_UNCOMPRESSED);

# ifdef SECP256K1_FLAGS_BIT_CONTEXT_COMPRESSION
  printf("defined !!!\n");
#endif


  return 0;
}

// types

// secp256k1_context
// secp256k1_pubkey
// secp256k1_ecdsa_signature
// secp256k1_nonce_function

// macros
//
// SECP256k1_GNUC_PREREQ(_x,_y)             ((4<<16)+9>=((_x)<<16)+(_y)) 
// __STDC_VERSION__                         undefined
// SECP256K1_INLINE                         __inline__
// SECP256K1_API                            defined 
// _WIN32                                   undefined
// SECP256K1_BUILD                          undefined 
// __GNUC__                                 4
// SECP256K1_WARN_UNUSED_RESULT             __attribute__ ((__warn_unused_result__))
// SECP256K1_ARG_NONNULL(_x)                __attribute__ ((__nonnull__(_x)))
// SECP256K1_FLAGS_TYPE_MASK                0xFF
// SECP256K1_FLAGS_TYPE_CONTEXT             1
// SECP256K1_FLAGS_TYPE_COMPRESSION         2
// SECP256K1_FLAGS_BIT_CONTEXT_VERIFY       0x100 (256)
// SECP256K1_FLAGS_BIT_CONTEXT_SIGN         0x200 (512)
// SECP256K1_FLAGS_BIT_CONTEXT_COMPRESSION  0x100 (256)
// SECP256K1_FLAGS_CONTEXT_VERIFY           0x101 (257)
// SECP256K1_FLAGS_CONTEXT_SIGN             0x201 (513)
// SECP256K1_FLAGS_CONTEXT_NONE             1
// SECP256K1_EC_COMPRESSED                  2
//
//
//
//
//
//



