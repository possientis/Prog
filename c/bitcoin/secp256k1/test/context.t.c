#include <stdio.h>
#include <assert.h>
#include "secp256k1.h"
#include "test.h"

static int test_context_create();
static int test_context_clone();
static int test_context_destroy();


int test_context()
{

  assert(test_context_create() == 0);
  assert(test_context_clone() == 0);
  assert(test_context_destroy() == 0);


  secp256k1_context *clone;
  secp256k1_context *new;


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

static int test_context_create()
{
  fprintf(stderr, "\ntesting creating contexts...\n");

  return 0;
}

static int test_context_clone()
{
  fprintf(stderr, "\ntesting cloning contexts...\n");

  return 0;
}
static int test_context_destroy()
{

  fprintf(stderr, "\ntesting destroying contexts...\n");

  return 0;
}
