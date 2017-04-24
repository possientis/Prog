#include <stdio.h>
#include <assert.h>
#include "secp256k1.h"
#include "test.h"

int test_callback()
{

  fprintf(stderr,"\ntesting setting up callbacks...\n");

  int call_back_data;
  secp256k1_context *ctx;
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create
      ( SECP256K1_CONTEXT_VERIFY 
      | SECP256K1_CONTEXT_SIGN
      );

  // secp256k1_context_set_illegal_callback
  secp256k1_context_set_illegal_callback(ctx,default_callback, &call_back_data);

  // secp2561k1_context_set_error_callback
  secp256k1_context_set_error_callback(ctx,default_callback, &call_back_data);

  secp256k1_context_destroy(ctx);

  return 0;
}


