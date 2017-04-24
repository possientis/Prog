#include <stdio.h>
#include <assert.h>
#include "secp256k1.h"

int test_context()
{

  secp256k1_context *ctx;
  secp256k1_context *clone;

  fprintf(stderr, "\ntesting contexts...\n");
  
  // SECP256K1_CONTEXT_VERIFY
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  // SECP2561K1_CONTEXT_SIGN
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  // SECP256K1_CONTEXT_NONE
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  return 0;

}


