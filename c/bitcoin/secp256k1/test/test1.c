#include "secp256k1.h"
#include <assert.h>

int main(){

  // valid key
  const unsigned char *pubkey_bytes = "\x03"
  "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
  "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // valid signature
  const unsigned char *sig_bytes = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\x0e\x5c\x6e\xc6\x54\x08\xd6\x5a\xae\x9e\x1c\xe8\xe9\x53\xc3\x1e"
    "\xd0\x3f\x41\x79\x09\x1d\x20\xd1\x59\xda\xe4\x19\xe9\x0c\xa3\x63";

  const unsigned char *hash_bytes = 
    "\x7f\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d"
    "\xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69";

  int value;
  secp256k1_context *ctx;
  secp256k1_pubkey pub;
  secp256k1_ecdsa_signature sig;

  
  ctx = secp256k1_context_create
      ( SECP256K1_CONTEXT_VERIFY 
      | SECP256K1_CONTEXT_SIGN
      );

  // parsing public key
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes, 33);
  assert(value == 1);

  // parsing signature
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig, sig_bytes);
  assert(value == 1);

  // verifying signature 
  value = secp256k1_ecdsa_verify(ctx, &sig, hash_bytes, &pub);
  assert(value == 1);

  // passing NULL context (SEGMENTATION FAULT)
  value = secp256k1_ecdsa_verify(NULL, &sig, hash_bytes, &pub);


  secp256k1_context_destroy(ctx);

  return 0;

}
