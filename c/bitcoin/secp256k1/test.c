#include "secp256k1/include/secp256k1.h"

#include <assert.h>
#include <stdio.h>


void default_callback(const char* message, void* data){
  fprintf(stderr, "default_callback: %s\n", message);
  *((int*) data) = 42;
}

int buffer_equals(const void *ptr, const void* qtr, size_t size)
{
  if(ptr == NULL) return 0;
  if(qtr == NULL) return 0;
  if(size < 0)    return 0;

  const unsigned char *p = ptr;
  const unsigned char *q = qtr;

  int i;
  for(i = 0; i < size; ++i)
  {
    if(*p++ != *q++) return 0;
  }
  return 1;
}


int main()
{

  secp256k1_context *ctx;         // pointer
  secp256k1_context *clone;       // pointer
  secp256k1_pubkey pub;           // 64 bytes

  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(ctx) == 8);
  assert(sizeof(clone) == 8);
  assert(sizeof(pub) == 64);
  assert(sizeof(sig1) == 64);
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
  call_back_data = 0;           // make sure next error correctly sets it

  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(return_value == 0);    // failing call
  assert(call_back_data == 42); // call back return value
  call_back_data = 0;           // make sure next error correctly sets it


  // pub1 and pub4 should parse into the same key
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub1, bytes1, 33);
  assert(return_value == 1);
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub2, bytes4, 65);
  assert(return_value == 1);
  assert(buffer_equals(&pub1, &pub2, sizeof(secp256k1_pubkey)));


  printf("testing serializing public key ...\n");

  unsigned char buffer[65];
  size_t size = 65;

  // compressed

  // serializing with output buffer too small
  size = 32;
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 0);  // should always be the case
  assert(size == 32);         // size unchanged here
  assert(call_back_data == 42); // call back return value
  call_back_data = 0;           // make sure next error correctly sets it


  // secp256k1_ec_pubkey_serialize
  size = 33;
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 1);  // should always be the case
  assert(size == 33);         // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes1, 33));

  // uncompressed
  
  // serializing with output buffer too small
  size = 64;
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 0);    // should always be the case
  assert(size == 64);           // size unchanged here
  assert(call_back_data == 42); // call back return value
  call_back_data = 0;           // make sure next error correctly sets it

  size = 65;
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 1);  // should always be the case
  assert(size == 65);         // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes4, 65));

  printf("testing parsing signature ...\n");

  const unsigned char* sig_bytes1 = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\x0e\x5c\x6e\xc6\x54\x08\xd6\x5a\xae\x9e\x1c\xe8\xe9\x53\xc3\x1e"
    "\xd0\x3f\x41\x79\x09\x1d\x20\xd1\x59\xda\xe4\x19\xe9\x0c\xa3\x63";

  // NULL context (still works)
  return_value = secp256k1_ecdsa_signature_parse_compact(NULL, &sig1, sig_bytes1); 
  assert(return_value == 1);  // succesful parse

  // NULL output pointer
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, NULL, sig_bytes1);  
  assert(return_value == 0);  // can't parse
  assert(call_back_data == 42);
  call_back_data = 0;           // make sure next error correctly sets it


  // NULL input pointer
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, NULL);  
  assert(return_value == 0);  // can't parse
  assert(call_back_data == 42);
  call_back_data = 0;           // make sure next error correctly sets it
  
  // secp256k1_ecdsa_signature_parse_compact
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);  
  assert(return_value == 1);  // succesful parse
  
  printf("testing serializing signature (DER) ...\n");
  unsigned char der[128];
  
  // NULL context
  size = 128;
  return_value = secp256k1_ecdsa_signature_serialize_der(NULL,der,&size,&sig1); 
  assert(return_value == 1);    // still works
  assert(size == 71);           // der serialization is 71 bytes in this case

  // NULL output pointer
  size = 128;
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,NULL,&size,&sig1); 
  assert(return_value == 0);    // can't serialize
  assert(size == 128);          // size unchanged
  assert(call_back_data == 42); // check callback return value
  call_back_data = 0;           // make sure next error correctly sets it
  
  // output pointer only 71 bytes
  size = 71;
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 1);      // still works
  assert(size == 71);

  // output pointer only 70 bytes (CALLBACK not being called)
  size = 70;
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 0);      // can't serialize
  assert(size == 71);             // size is changed here 
  assert(call_back_data == 0);    // CALLBACK IS NOT CALLED !
  call_back_data = 0;             // make sure next error correctly sets it

  // null input pointer
  size = 128;
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,NULL); 
  assert(return_value == 0);      // can't serialize
  assert(size == 128);            // size is unchanged
  assert(call_back_data == 42);   // checking callback return value
  call_back_data = 0;             // make sure next error correctly sets it

  // secp256k1_ecdsa_signature_serialize_der
  size = 128;
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 1);
  assert(size == 71);
  assert(call_back_data == 0);    // unaffected by call
 

  printf("testing parsing DER signature ...\n");

  // NULL context 
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(NULL,&sig,der,size); 
  assert(return_value == 1);      // parsing was succesful
  assert(buffer_equals(&sig1, &sig, sizeof(secp256k1_ecdsa_signature)));

  // NULL input pointer
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,NULL,size); 
  assert(return_value == 0);      // can't parse

  // NULL output pointer
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(return_value == 0);      // can't parse

  // wrong size input
  size = 70;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(return_value == 0);      // can't parse
  assert(size == 70);             // size unchanged

  // secp256k1_ecdsa_signature_parse_der
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,&sig2,der,size); 
  assert(return_value == 1);      // parsing was succesful
  assert(buffer_equals(&sig1, &sig2, sizeof(secp256k1_ecdsa_signature)));

  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);


}


