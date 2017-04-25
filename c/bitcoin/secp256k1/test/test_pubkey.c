#include <stdio.h>
#include <assert.h>
#include "secp256k1.h"
#include "test.h"

int test_pubkey()
{
  secp256k1_pubkey pub;
  int value;

  assert(sizeof(pub) == 64);

  fprintf(stderr,"\ntesting parsing public key...\n");

  // secp256k1_ec_pubkey_parse
  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes1, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes2, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes3, 33); 
  assert(value == 0);         // public key is invalid
  assert(callback_data == 0); // but no error

  return 0;
}


