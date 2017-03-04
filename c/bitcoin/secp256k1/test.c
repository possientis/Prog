#include "secp256k1/include/secp256k1.h"


#include <assert.h>
#include <stdio.h>

void default_callback(const char* message, void* data){
  printf("default_callback: %s\n", message);
  *((int*) data) = 42;
}

int main()
{
  secp256k1_context *ctx;         // pointer
  secp256k1_context *clone;       // pointer
  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(ctx) == 8);
  assert(sizeof(clone) == 8);
  assert(sizeof(pub) == 64);
  assert(sizeof(sig) == 64);
  assert(sizeof(fun) == 8);

  printf("testing contexts ...\n");

  ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  assert(ctx != NULL);
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  assert(ctx != NULL);
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  assert(ctx != NULL);
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  printf("testing callbacks ...\n");
  int return_value;
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  secp256k1_context_set_illegal_callback(ctx,default_callback, &return_value);
  secp256k1_context_set_error_callback(ctx,default_callback, &return_value);
  secp256k1_context_destroy(ctx);

  printf("testing parsing public key ...\n");
// "03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
// "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
//   "07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",

}


