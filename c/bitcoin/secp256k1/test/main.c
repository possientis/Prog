#include <assert.h>
#include <stdio.h>
#include <string.h>

#include <secp256k1.h>
#include "test.h"



int main()
{
  assert(test_setup() == 0);
  assert(test_macro() == 0);
  assert(test_context() == 0);
  assert(test_callback() == 0);
  assert(test_ec_seckey() == 0);
  assert(test_ec_pubkey() == 0);
  assert(test_ecdsa_signature() == 0);
  assert(test_nonce_function() == 0);

  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_ecdsa_signature sig3;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer


  int value;
  unsigned char buffer[65];
  size_t size = 65;
  unsigned char nonce1[32];
  unsigned char nonce2[32];

  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);
  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;


  fprintf(stderr,"\ntesting context_randomize...\n");
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_context_randomize(ctx, priv_bytes1);
  assert(value == 1);

  fprintf(stderr,"\ntesting pubkey_combine...\n");
  // not doing much here
  memcpy(&pub2, &pub1, 64);
  const secp256k1_pubkey* const list[2] = { &pub1, &pub2 };
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_combine(ctx, &pub, list, 2);
  assert(value == 1);
  
  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);

  return 0;

}
