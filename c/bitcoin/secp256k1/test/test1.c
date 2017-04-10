#include "secp256k1.h"
#include <assert.h>

int main()
{
  int return_value;

  secp256k1_context *ctx;         
  secp256k1_pubkey pub;           

  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);

  // This is a valid public key
  const unsigned char *pub1 = "\x03"
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub1, 33); 
  assert(return_value == 1);  // public key is indeed valid

  // same call with NULL context
  return_value = secp256k1_ec_pubkey_parse(NULL, &pub, pub1, 33); 
  assert(return_value == 1);  // call is successfull

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
}


