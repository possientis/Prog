#include <stdio.h>
#include <assert.h>
#include <secp256k1.h>
#include "test.h"

static int test_context_create(int);
static int test_context_clone();
static int test_context_destroy();
static int test_context_randomize();


int test_context()
{

  assert(test_context_create(SECP256K1_CONTEXT_VERIFY) == 0);
  assert(test_context_create(SECP256K1_CONTEXT_SIGN) == 0);
  assert(test_context_create(SECP256K1_CONTEXT_NONE) == 0);
  assert(test_context_clone() == 0);
  assert(test_context_destroy() == 0);
  assert(test_context_randomize() == 0);

  return 0;

}

static int test_context_create(int flag)
{

  secp256k1_context *new;

  const char *str;

  switch(flag) {
    case SECP256K1_CONTEXT_NONE:
      str = "(None)"; break;
    case SECP256K1_CONTEXT_SIGN: 
      str = "(Sign)"; break;
    case SECP256K1_CONTEXT_VERIFY:
      str = "(Verify)"; break;
    default:
      assert(0);
  }
 
  fprintf(stderr, "\ntesting creating contexts %s...\n", str);
  new = secp256k1_context_create(flag);
  secp256k1_context_destroy(new);

  return 0;
}

static int test_context_clone()
{
  secp256k1_context *new, *clone;

  fprintf(stderr, "\ntesting cloning contexts...\n");

  new = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  clone = secp256k1_context_clone(new);
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  new = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  clone = secp256k1_context_clone(new);
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  new = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  clone = secp256k1_context_clone(new);
  secp256k1_context_destroy(new);
  secp256k1_context_destroy(clone);

  return 0;
}

static int test_context_destroy()
{
  fprintf(stderr, "\ntesting destroying contexts...\n");
  // nothing
  return 0;
}

static int test_context_randomize()
{

  int value;

  fprintf(stderr,"\ntesting context_randomize...\n");
  
  /*  
  // NULL ctx (segmentation fault)
  callback_data.in = "context_randomize.1";
  callback_data.out = 0;
  value = secp256k1_context_randomize(NULL, priv_bytes1);
  assert(value == 0);
  assert(callback_data.out == 42);
  */
  
  // NULL input pointer (reset to initial state)
  callback_data.in = "context_randomize.1";
  callback_data.out = 0;
  value = secp256k1_context_randomize(ctx, NULL);
  assert(value == 1);
  assert(callback_data.out == 0);

  // normal call
  callback_data.in = "context_randomize.0";
  callback_data.out = 0;
  value = secp256k1_context_randomize(ctx, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);

  return 0;
}




