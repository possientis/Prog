#include <stdio.h>
#include <assert.h>
#include "secp256k1.h"
#include "test.h"

int test_context()
{

  secp256k1_context *clone;
  secp256k1_context *new;

  fprintf(stderr, "\ntesting contexts...\n");

  assert(sizeof(new) == 8);
  
  // SECP256K1_CONTEXT_VERIFY
  
  // secp2561k1_context_create
  new = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  assert(new != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(new);
  assert(clone != NULL);
  assert(clone != new);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  // SECP2561K1_CONTEXT_SIGN
  
  // secp2561k1_context_create
  new = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  assert(new != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(new);
  assert(clone != NULL);
  assert(clone != new);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  // SECP256K1_CONTEXT_NONE
  
  // secp2561k1_context_create
  new = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  assert(new != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(new);
  assert(clone != NULL);
  assert(clone != new);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  return 0;

}


