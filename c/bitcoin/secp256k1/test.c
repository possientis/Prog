#include "secp256k1/include/secp256k1.h"


#include <assert.h>
#include <stdio.h>

void default_callback(const char* message, void* data){
  printf("default_callback: %s\n", message);
  *((int*) data) = 42;
}

int main()
{

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
  int call_back_data;
 
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);

  // secp256k1_context_set_illegal_callback
  secp256k1_context_set_illegal_callback(ctx,default_callback, &call_back_data);

  // secp2561k1_context_set_error_callback
  secp256k1_context_set_error_callback(ctx,default_callback, &call_back_data);



  printf("testing parsing public key ...\n");

  int return_value;

// "03f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
// "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a"
//   "07cf33da18bd734c600b96a72bbc4749d5141c90ec8ac328ae52ddfe2e505bdb",
  
  const unsigned char *bytes1 = "\x03"
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes1, 33); 
  assert(return_value == 1);  // public key is valid


  const unsigned char *bytes2 = "\x02"  // this key is still valid
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";
  
  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes2, 33); 
  assert(return_value == 1);  // public key is valid


  const unsigned char *bytes3 = "\x04"  // this key is invalid: 0x04 => 65 bytes
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes3, 33); 
  assert(return_value == 0);  // public key is invalid


  const unsigned char *bytes4 = "\x04"  // this key is valid
    "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a"
    "\x07\xcf\x33\xda\x18\xbd\x73\x4c\x60\x0b\x96\xa7\x2b\xbc\x47\x49"
    "\xd5\x14\x1c\x90\xec\x8a\xc3\x28\xae\x52\xdd\xfe\x2e\x50\x5b\xdb";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes4, 65); 
  assert(return_value == 1);  // public key is valid


  const unsigned char *bytes5 = "\x04"  // this key is invalid (typo \xff)
    "\xff\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a"
    "\x07\xcf\x33\xda\x18\xbd\x73\x4c\x60\x0b\x96\xa7\x2b\xbc\x47\x49"
    "\xd5\x14\x1c\x90\xec\x8a\xc3\x28\xae\x52\xdd\xfe\x2e\x50\x5b\xdb";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes5, 65); 
  assert(return_value == 0);  // public key is invalid

  
  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(NULL, &pub, bytes4, 65); 
  assert(return_value == 1);  // SUCCESSFUL DESPITE NULL CONTEXT

  // secp256k1_ec_pubkey_parse (NULL secp256k1_pubkey pointer)
  return_value = secp256k1_ec_pubkey_parse(ctx, NULL, bytes4, 65); 
  assert(return_value == 0);    // failing call
  assert(call_back_data == 42); // call back return value

  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(return_value == 0);    // failing call
  assert(call_back_data == 42); // call back return value


  // pub1 and pub4 should parse into the same key
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub1, bytes1, 33);
  assert(return_value == 1);
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub2, bytes4, 65);
  assert(return_value == 1);
  const unsigned char* ptr = (unsigned char*) &pub1;
  const unsigned char* qtr = (unsigned char*) &pub2;

  int i;
  for(i = 0; i < sizeof(secp256k1_pubkey); ++i)
  {
    assert(*ptr++ == *qtr++);
  }

  printf("testing serializing public key ...\n");

  unsigned char buffer[65];
  size_t size = 65;

  // compressed
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 1);  // should always be the case
  assert(size == 33);         // expecting 33 bytes written
  ptr = buffer;
  qtr = bytes1;
  for(i = 0; i < 33; ++i)
  {
    assert(*ptr++ == *qtr++);
  }

  // uncompressed
  size = 65;
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 1);  // should always be the case
  assert(size == 65);         // expecting 33 bytes written
  ptr = buffer;
  qtr = bytes4;
  for(i = 0; i < 65; ++i)
  {
    assert(*ptr++ == *qtr++);
  }


  printf("testing parsing signature ...\n");
  
  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);


}


