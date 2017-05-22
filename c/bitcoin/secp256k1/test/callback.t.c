#include <stdio.h>
#include <assert.h>
#include <secp256k1.h>
#include "test.h"

int test_callback()
{

  fprintf(stderr,"\ntesting setting up callbacks...\n");

  callback_t data;

  data.in = "This is an error message";

  secp256k1_context *new;
  
  // secp2561k1_context_create
  new = secp256k1_context_create
      ( SECP256K1_CONTEXT_VERIFY 
      | SECP256K1_CONTEXT_SIGN
      );

  // secp256k1_context_set_illegal_callback
  secp256k1_context_set_illegal_callback(new,default_callback, &data);

  // secp2561k1_context_set_error_callback
  secp256k1_context_set_error_callback(new,default_callback, &data);

  secp256k1_context_destroy(new);

  return 0;
}


