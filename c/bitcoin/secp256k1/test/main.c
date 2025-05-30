#include <assert.h>
#include <stdio.h>
#include <string.h>

#include <secp256k1.h>
#include "test.h"



int main()
{
  fprintf(stderr, "******************************************************************\n");
#if CLONE
  fprintf(stderr, "*                   Testing cloned library                       *\n");
#else
  fprintf(stderr, "*                    Testing main library                        *\n");
#endif
  fprintf(stderr, "******************************************************************\n");

#if CLONE  
  assert(secp256k1_check());
#endif

  assert(test_setup() == 0);
  assert(test_macro() == 0);
  assert(test_context() == 0);
  assert(test_callback() == 0);
  assert(test_ec_seckey() == 0);
  assert(test_ec_pubkey() == 0);
  assert(test_ecdsa_signature() == 0);
  assert(test_nonce_function() == 0);
  assert(test_cleanup() == 0);

  return 0;

}
