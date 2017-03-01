#include "secp256k1/include/secp256k1.h"


#include <assert.h>
#include <stdio.h>

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

}


