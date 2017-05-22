#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <secp256k1.h>
#include "test.h"

int test_nonce_function()
{

  unsigned char nonce1[32];
  unsigned char nonce2[32];
  int value;

  memset(nonce1,0x00, 32);
  memset(nonce2,0x00, 32);

  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;

  fprintf(stderr,"\ntesting rfc6979 nonce function...\n");

  assert(sizeof(f1) == 8);
  assert(sizeof(f2) == 8);

  callback_data.in = "nonce_function.0";
  callback_data.out = 0;
  value = f1(nonce1, hash_bytes1, priv_bytes1, NULL, NULL, 0);
  assert(value == 1);
  callback_data.in = "nonce_function.0";
  callback_data.out = 0;
  value = f2(nonce2, hash_bytes1, priv_bytes1, NULL, NULL, 0);
  assert(value == 1);
 
  // making sure f1 and f2 coincide
  assert(memcmp(nonce1, nonce2, 32) == 0);
  // validating result
  assert(memcmp(nonce1, nonce_bytes1, 32) == 0);

  // WARNING: NULL pointers will lead to segmentation fault
  // value = f1(NULL, hash_bytes1, priv_bytes1, NULL, NULL, 0);
  // value = f1(nonce1, NULL, priv_bytes1, NULL, NULL, 0);
  // value = f1(nonce1, hash_bytes1, NULL, NULL, NULL, 0);

  return 0;
}

