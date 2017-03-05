#include "secp256k1/include/secp256k1.h"


#include <assert.h>
#include <stdio.h>

void default_callback(const char* message, void* data){
  printf("default_callback: %s\n", message);
  *((int*) data) = 42;
}

int main()
{
  int call_back_data;
  int return_value;

  secp256k1_context *ctx;         // pointer
  secp256k1_context *clone;       // pointer
  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(ctx) == 8);
  assert(sizeof(clone) == 8);
  assert(sizeof(pub) == 64);
  assert(sizeof(sig) == 64);
  assert(sizeof(fun) == 8);

  printf("testing contexts ...\n");

  // SECP256K1_CONTEXT_VERIFY
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  // SECP2561K1_CONTEXT_SIGN
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  // SECP256K1_CONTEXT_NONE
  
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  assert(ctx != NULL);

  // secp2561k1_context_clone
  clone = secp256k1_context_clone(ctx);
  assert(clone != NULL);
  assert(clone != ctx);

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);
  secp256k1_context_destroy(clone);

  printf("testing callbacks ...\n");

  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);

  // secp256k1_context_set_illegal_callback
  secp256k1_context_set_illegal_callback(ctx,default_callback, &call_back_data);

  // secp2561k1_context_set_error_callback
  secp256k1_context_set_error_callback(ctx,default_callback, &call_back_data);



  printf("testing parsing public key ...\n");
// "03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
// "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
//   "07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
  
  const unsigned char *pub1 = "\x03"
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub1, 33); 
  assert(return_value == 1);  // public key is valid


  const unsigned char *pub2 = "\x02"  // this key is still valid
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";
  
  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub2, 33); 
  assert(return_value == 1);  // public key is valid


  const unsigned char *pub3 = "\x04"  // this key is invalid: 0x04 => 65 bytes
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub3, 33); 
  assert(return_value == 0);  // public key is invalid


  const unsigned char *pub4 = "\x04"  // this key is valid
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a"
    "\x07\xcf\x33\xda\x18\xbd\x73\x4c\x60\x0b\x96\xa7\x2b\xbc\x47\x49"
    "\xd5\x14\x1c\x90\xec\x8a\xc3\x28\xae\x52\xdd\xfe\x2e\x50\x5b\xdb";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub4, 65); 
  assert(return_value == 1);  // public key is invalid


  const unsigned char *pub5 = "\x04"  // this key is invalid (typo \xff)
    "\xff\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a"
    "\x07\xcf\x33\xda\x18\xbd\x73\x4c\x60\x0b\x96\xa7\x2b\xbc\x47\x49"
    "\xd5\x14\x1c\x90\xec\x8a\xc3\x28\xae\x52\xdd\xfe\x2e\x50\x5b\xdb";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, pub5, 65); 
  assert(return_value == 0);  // public key is invalid

 
  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(NULL, &pub, pub4, 65); 
  assert(return_value == 1);  // public key is valid

  // secp256k1_ec_pubkey_parse (NULL secp256k1_pubkey pointer)
  return_value = secp256k1_ec_pubkey_parse(ctx, NULL, pub4, 65); 
  assert(return_value == 0);    // failing call
  assert(call_back_data == 42); // call back return value

  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(return_value == 0);    // failing call
  assert(call_back_data == 42); // call back return value

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);


}


