#include "secp256k1/include/secp256k1.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>


void default_callback(const char* message, void* data){
  fprintf(stderr, "callback function is rightly called: %s\n", message);
  *((int*) data) = 42;
}

int buffer_equals(const void *ptr, const void* qtr, size_t size)
{
  if(ptr == NULL) return 0;
  if(qtr == NULL) return 0;
  if(size < 0)    return 0; // should be ignored by compiler if size_t unsigned

  const unsigned char *p = ptr;
  const unsigned char *q = qtr;

  size_t i;
  for(i = 0; i < size; ++i)
  {
    if(*p++ != *q++) return 0;
  }
  return 1;
}

int buffer_null(const void *ptr, size_t size)
{
  if(ptr == NULL) return 0;
  if(size < 0) return 0;

  const unsigned char *p = ptr;

  size_t i;
  for(i = 0; i < size; ++i)
  {
    if( *p++ != '\x00' ) return 0;
  }

  return 1;
}

void buffer_clear(void *ptr, size_t size){
  if(ptr == NULL) return;
  if(size < 0)  return;   // should be ignored by compiler if size_t unsigned 

  unsigned char *p = ptr;
  
  size_t i;
  for(i = 0; i < size; ++i)
  {
    *p++ = '\x00';
  }
}


int main()
{

  secp256k1_context *ctx;         // pointer
  secp256k1_context *clone;       // pointer
  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
 
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_ecdsa_signature sig3;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(ctx) == 8);
  assert(sizeof(clone) == 8);
  assert(sizeof(pub) == 64);
  assert(sizeof(sig1) == 64);
  assert(sizeof(fun) == 8);

  printf("\ntesting contexts ...\n");

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

  printf("\ntesting setting up callbacks ...\n");
  int call_back_data;
 
  // secp2561k1_context_create
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_SIGN);

  // secp256k1_context_set_illegal_callback
  secp256k1_context_set_illegal_callback(ctx,default_callback, &call_back_data);

  // secp2561k1_context_set_error_callback
  secp256k1_context_set_error_callback(ctx,default_callback, &call_back_data);


  printf("\ntesting parsing public key ...\n");

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

  const unsigned char *bytes6 = "\x03" // typo first byte, but valid
    "\xff\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
    "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";

  // secp256k1_ec_pubkey_parse
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub, bytes5, 65); 
  assert(return_value == 0);        // public key is invalid
//  assert(call_back_data == 42);   // CALLBACK IS NOT CALLED (WRONG?)
  call_back_data = 0;
  
  // secp256k1_ec_pubkey_parse (NULL context)
  return_value = secp256k1_ec_pubkey_parse(NULL, &pub, bytes4, 65); 
  assert(return_value == 1);        // SUCCESSFUL DESPITE NULL CONTEXT
  assert(call_back_data == 0);      // unaffected by call

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
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub1, bytes1, 33);
  assert(return_value == 1);
  return_value = secp256k1_ec_pubkey_parse(ctx, &pub2, bytes4, 65);
  assert(return_value == 1);
  assert(buffer_equals(&pub1, &pub2, sizeof(secp256k1_pubkey)));


  printf("\ntesting serializing public key ...\n");

  unsigned char buffer[65];
  size_t size = 65;

  // compressed
  printf("compressed format ...\n");
  // serializing with output buffer too small
  size = 32;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 0);        // serialization failed (WRONG DOCUMENTATION) 
  assert(size == 32);               // size unchanged here
  assert(buffer_null(buffer, 65));  // output buffer unaffected 
  assert(call_back_data == 42);     // call back return value
  call_back_data = 0;               // make sure next error correctly sets it

  // NULL context
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      NULL, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 1);                  // serialization succeeded
  assert(size == 33);                         // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes1, 33));  // success despite NULL context
  assert(call_back_data == 0);                // unaffected by call

  // NULL output buffer
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, NULL, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(buffer_null(buffer, 65));  // output buffer unaffected
  assert(call_back_data == 42);     // call back return value
  call_back_data = 0;               // make sure next error correctly sets it

  // NULL input pubkey pointer
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, NULL, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(buffer_null(buffer, 65));  // output buffer unaffected
  assert(call_back_data == 42);     // call back return value
  call_back_data = 0;               // make sure next error correctly sets it


  // secp256k1_ec_pubkey_serialize
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(return_value == 1);        // should always be the case
  assert(size == 33);               // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes1, 33));
  assert(call_back_data == 0);      // unaffected by call

  // uncompressed
  printf("uncompressed format ...\n");
  
  // serializing with output buffer too small
  size = 64;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 0);    // should always be the case
  assert(size == 64);           // size unchanged here
  assert(buffer_null(buffer, 65));  // output buffer unaffected
  assert(call_back_data == 42); // call back return value
  call_back_data = 0;           // make sure next error correctly sets it

  // NULL context
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      NULL, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 1);                  // serialization succeeded
  assert(size == 65);                         // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes4, 65));  // success despite NULL context
  assert(call_back_data == 0);                // unaffected by call

  // NULL output buffer
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, NULL, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(buffer_null(buffer, 65));  // output buffer unaffected
  assert(call_back_data == 42);     // call back return value
  call_back_data = 0;               // make sure next error correctly sets it

  // NULL input pubkey pointer
  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, NULL, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(buffer_null(buffer, 65));  // output buffer unaffected
  assert(call_back_data == 42);     // call back return value
  call_back_data = 0;               // make sure next error correctly sets it


  size = 65;
  buffer_clear(buffer, 65);
  return_value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(return_value == 1);        // should always be the case
  assert(size == 65);               // expecting 33 bytes written
  assert(buffer_equals(buffer, bytes4, 65));
  assert(call_back_data == 0);      // unaffected by call


  printf("\ntesting parsing signature (compact) ...\n");

  const unsigned char* sig_bytes1 = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\x0e\x5c\x6e\xc6\x54\x08\xd6\x5a\xae\x9e\x1c\xe8\xe9\x53\xc3\x1e"
    "\xd0\x3f\x41\x79\x09\x1d\x20\xd1\x59\xda\xe4\x19\xe9\x0c\xa3\x63";

  // NULL context (still works)
  return_value = secp256k1_ecdsa_signature_parse_compact(NULL, &sig1, sig_bytes1); 
  assert(return_value == 1);      // parsing succeeded
  assert(call_back_data == 0);    // unaffected by call

  // NULL output pointer
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, NULL, sig_bytes1);  
  assert(return_value == 0);      // parsing failed
  assert(call_back_data == 42);   // callback return value
  call_back_data = 0;             // make sure next error correctly sets it


  // NULL input pointer
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, NULL);  
  assert(return_value == 0);      // parsing failed
  assert(call_back_data == 42);   // callback return value
  call_back_data = 0;             // make sure next error correctly sets it
  
  // secp256k1_ecdsa_signature_parse_compact
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);  
  assert(return_value == 1);      // parsing succeeded
  assert(call_back_data == 0);    // unaffected by call
  

  printf("\ntesting serializing signature (DER) ...\n");
  unsigned char der[128];
  
  // NULL context
  size = 128;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(NULL,der,&size,&sig1); 
  assert(return_value == 1);      // serialization succeeded
  assert(size == 71);             // der serialization is 71 bytes in this case
  assert(call_back_data == 0);    // unaffected by call

  // NULL output pointer
  size = 128;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,NULL,&size,&sig1); 
  assert(return_value == 0);      // serialization failed
  assert(size == 128);            // size unchanged
  assert(buffer_null(der, 128));  // output buffer unaffected
  assert(call_back_data == 42);   // check callback return value
  call_back_data = 0;             // make sure next error correctly sets it
  
  // output pointer only 71 bytes
  size = 71;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 1);      // serialization succeeded
  assert(size == 71);
  assert(call_back_data == 0);    // unaffected by call

  // output pointer only 70 bytes (CALLBACK not being called)
  size = 70;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 0);      // can't serialize
  assert(size == 71);             // size is changed here 
  assert(buffer_null(der, 128));  // output buffer unaffected
  assert(call_back_data == 0);    // CALLBACK IS NOT CALLED ! (WRONG)
  call_back_data = 0;             // make sure next error correctly sets it

  // null input pointer
  size = 128;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,NULL); 
  assert(return_value == 0);      // can't serialize
  assert(size == 128);            // size is unchanged
  assert(buffer_null(der, 128));  // output buffer unaffected
  assert(call_back_data == 42);   // checking callback return value
  call_back_data = 0;             // make sure next error correctly sets it

  // secp256k1_ecdsa_signature_serialize_der
  size = 128;
  buffer_clear(der, 128);
  return_value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(return_value == 1);
  assert(size == 71);
  assert(call_back_data == 0);    // unaffected by call
 

  printf("\ntesting parsing signature (DER) ...\n");

  // NULL context 
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(NULL,&sig,der,size); 
  assert(return_value == 1);      // parsing was succesful
  assert(buffer_equals(&sig1, &sig, sizeof(secp256k1_ecdsa_signature)));

  // NULL input pointer
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,NULL,size); 
  assert(return_value == 0);      // can't parse
  assert(call_back_data == 42); 
  call_back_data = 0;             // make sure next error correctly sets it

  // NULL output pointer
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(return_value == 0);      // can't parse
  assert(call_back_data == 42);    
  call_back_data = 0;             // make sure next error correctly sets it

  // wrong size input
  size = 70;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(return_value == 0);      // can't parse
  assert(size == 70);             // size unchanged
  assert(call_back_data == 42);    
  call_back_data = 0;             // make sure next error correctly sets it

  // secp256k1_ecdsa_signature_parse_der
  size = 71;
  return_value = secp256k1_ecdsa_signature_parse_der(ctx,&sig2,der,size); 
  assert(return_value == 1);      // parsing was succesful
  assert(buffer_equals(&sig1, &sig2, sizeof(secp256k1_ecdsa_signature)));

  printf("\ntesting serializing signature (compact) ...\n");

  unsigned char buffer64[64];

  // NULL context
  buffer_clear(buffer64, 64);
  return_value = secp256k1_ecdsa_signature_serialize_compact(NULL,buffer64,&sig1);
  assert(return_value ==1);                       // serialization succeeded
  assert(buffer_equals(buffer64,sig_bytes1,64));  // initial signature
  assert(call_back_data == 0);

  // NULL output buffer
  buffer_clear(buffer64, 64);
  return_value = secp256k1_ecdsa_signature_serialize_compact(ctx,NULL,&sig1);
  assert(return_value ==0);                       // serialization failed
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL input signature pointer
  buffer_clear(buffer64, 64);
  return_value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer64,NULL);
  assert(return_value ==0);                       // serialization failed
  assert(call_back_data == 42);
  call_back_data = 0;

  
  // secp2561_ecdsa_signature_serialize_compact
  buffer_clear(buffer64, 64);
  return_value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer64,&sig1);
  assert(return_value ==1);                       // serialization succeeded
  assert(buffer_equals(buffer64,sig_bytes1,64));  // initial signature
  assert(call_back_data == 0);

  printf("\ntesting verifying signature ...\n");
  
  const unsigned char *hash1 = 
    "\x7f\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d"
    "\xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69";

  const unsigned char *hash2 =  /* typo in first byte */
    "\xff\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d"
    "\xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69";

  // NULL context (segmentation fault)
//  return_value = secp256k1_ecdsa_verify(NULL, &sig1, hash1, &pub1); 
//  assert(return_value == 1);
 // assert(call_back_data == 0);

  // NULL signature pointer
  return_value = secp256k1_ecdsa_verify(ctx, NULL, hash1, &pub1); 
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL msg32 pointer
  return_value = secp256k1_ecdsa_verify(ctx, &sig1, NULL, &pub1); 
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL pubkey pointer
  return_value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, NULL); 
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // wrong message
  return_value = secp256k1_ecdsa_verify(ctx, &sig1, hash2, &pub1); 
  assert(return_value == 0);    // verification failes
  assert(call_back_data == 0);  // but this is not an error, callback not called

  // wrong pubkey
  return_value = secp256k1_ec_pubkey_parse(ctx,&pub2, bytes6, 33);
  assert(return_value == 1);
  return_value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub2); 
  assert(return_value == 0);    // verification fails
  assert(call_back_data == 0);  // but not an error

  // secp256k1_ecdsa_verify
  return_value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub1); 
  assert(return_value == 1);
  assert(call_back_data == 0);

  printf("\ntesting normalizing signature ...\n");


  // non-normalized counterpart of sig_bytes1
  const unsigned char* sig_bytes2 = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\xf1\xa3\x91\x39\xab\xf7\x29\xa5\x51\x61\xe3\x17\x16\xac\x3c\xdf"
    "\xea\x6f\x9b\x6d\xa6\x2b\x7f\x6a\x65\xf7\x7a\x72\xe7\x29\x9d\xde";

  // parsing key
  return_value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);
  assert(return_value == 1);  // parsing successful 

  // key not normalized, hence signature verification should fail
  return_value = secp256k1_ecdsa_verify(ctx, &sig2, hash1, &pub1);
  assert(return_value == 0);  // verification fails 

  // normalizing sig2
  return_value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig2);
  assert(return_value == 1);                  // sig2 was *not* normalized
  assert(buffer_equals(&sig1, &sig3, 64));    // sig1 == sig3

  // normalizing sig1
  return_value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig1);
  assert(return_value == 0);                  // sig1 was already normalized

  // NULL context
  return_value = secp256k1_ecdsa_signature_normalize(NULL, &sig3, &sig2);
  assert(return_value == 1);                  // sig2 was *not* normalized

  // NULL ouput (only testing sig2 for normality)
  return_value = secp256k1_ecdsa_signature_normalize(ctx, NULL, &sig2);
  assert(return_value == 1);                  // sig2 was *not* normalized

  // NULL input
  return_value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, NULL);
  assert(return_value == 0);                  // not meaningful
  assert(call_back_data == 42);
  call_back_data = 0;



  printf("\ntesting rfc6979 nonce function ...\n");

  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;

  unsigned char nonce1[32];
  unsigned char nonce2[32];

  buffer_clear(nonce1, 32);
  buffer_clear(nonce2, 32);

  return_value = f1(nonce1, hash1, hash2, NULL, NULL, 0);
  assert(return_value == 1);

  return_value = f2(nonce2, hash1, hash2, NULL, NULL, 0);
  assert(return_value == 1);

  assert(buffer_equals(nonce1, nonce2, 32));

  // private key from Mastering Bitcoin
  const unsigned char* priv1 =
    "\x1e\x99\x42\x3a\x4e\xd2\x76\x08\xa1\x5a\x26\x16\xa2\xb0\xe9\xe5"
    "\x2c\xed\x33\x0a\xc5\x30\xed\xcc\x32\xc8\xff\xc6\xa5\x26\xae\xdd";

  return_value = f1(nonce1, hash1, priv1, NULL, NULL, 0); 
  assert(return_value == 1);

  return_value = f2(nonce2, hash1, priv1, NULL, NULL, 0); 
  assert(return_value == 1);
 
  // see java EC_Test_Utils.getDeterministicKey and Test18.java
  const unsigned char* nonce = 
    "\x8b\x87\x1e\x0f\x28\x6b\x37\x91\xab\xb6\xe1\xd7\xc2\x8e\x6c\x7e"
    "\x07\x19\x82\x9e\xfc\x03\xf6\x09\x4f\x70\xda\xb1\xb0\xf0\x0e\xfb";

  assert(buffer_equals(nonce1, nonce, 32));
  assert(buffer_equals(nonce2, nonce, 32));

  // NULL output pointer (segmentation fault: WRONG?)
  // return_value = f1(NULL, hash1, priv1, NULL, NULL, 0); 

  // NULL message pointer (segmentation fault: WRONG?)
  // return_value = f1(nonce1, NULL, priv1, NULL, NULL, 0); 

  // NULL key pointer (segmentation fault: WRONG?)
  // return_value = f1(nonce1, hash1, NULL, NULL, NULL, 0); 

  printf("\ntesting ecdsa signature generation ...\n");

  // NULL context: segmentation fault
//  return_value = secp256k1_ecdsa_sign(NULL, &sig, hash1, priv1, f1, NULL);

  // NULL output pointer
  return_value = secp256k1_ecdsa_sign(ctx, NULL, hash1, priv1, f1, NULL);
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL message pointer
  return_value = secp256k1_ecdsa_sign(ctx, &sig, NULL, priv1, f1, NULL);
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL priv1ate key pointer
  return_value = secp256k1_ecdsa_sign(ctx, &sig, hash1, NULL, f1, NULL);
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL nonce function pointer
  buffer_clear(&sig, 64);
  return_value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, NULL, NULL);
  assert(return_value == 1);  // signing successful (default nonce is used)
  assert(buffer_equals(&sig,&sig1,64));
  assert(call_back_data == 0);

  // secp256k1_ecdsa_sign
  buffer_clear(&sig, 64);
  return_value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, f1, NULL);
  assert(return_value == 1);
  assert(buffer_equals(&sig,&sig1,64));
  assert(call_back_data == 0);

  printf("\ntesting veryfying secret keys ...\n");

  const unsigned char* order = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";
  
  // curve order is not a valid private key
  return_value = secp256k1_ec_seckey_verify(ctx, order);
  assert(return_value == 0);
  assert(call_back_data == 0);

  const unsigned char* order_minus_one = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x40";

  // curve order less one is a valid private key
  return_value = secp256k1_ec_seckey_verify(ctx, order_minus_one);
  assert(return_value == 1);
  assert(call_back_data == 0);

  // zero is not a valid private key
  buffer_clear(nonce1, 32);
  return_value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(return_value == 0);
  assert(call_back_data == 0);

  // one is a valid private key
  buffer_clear(nonce1, 32);
  nonce1[31] = 0x01;
  return_value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(return_value == 1);
  assert(call_back_data == 0);

  // 2^32 -1 is not a valid private key
  int i;
  for(i = 0; i < 32; ++i)
    nonce1[i] = 0xff;
  return_value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(return_value == 0);
  assert(call_back_data == 0);

  // NULL context
  return_value = secp256k1_ec_seckey_verify(NULL, priv1);
  assert(return_value == 1);
  assert(call_back_data == 0);

  // Mastering Bitcoin private key is valid
  return_value = secp256k1_ec_seckey_verify(ctx, priv1);
  assert(return_value == 1);
  assert(call_back_data == 0);

 
  printf("\ntesting public key creation from private key ...\n");

  // NULL context: segmentation fault
//  return_value = secp256k1_ec_pubkey_create(NULL, &pub, priv1);

  // NULL output buffer
  return_value = secp256k1_ec_pubkey_create(ctx, NULL, priv1);
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // NULL private key pointer
  return_value = secp256k1_ec_pubkey_create(ctx, &pub, NULL);
  assert(return_value == 0);
  assert(call_back_data == 42);
  call_back_data = 0;

  // invalid private key
  return_value = secp256k1_ec_pubkey_create(ctx, &pub, order);
  assert(return_value == 0);    // failure
  assert(call_back_data == 0);  // but not an error

  // secp256k1_ec_pubkey_create
  buffer_clear(&pub, 64);
  return_value = secp256k1_ec_pubkey_create(ctx, &pub, priv1);
  assert(return_value == 1);
  assert(call_back_data == 0);
  assert(buffer_equals(&pub, &pub1, 64));

  printf("\ntesting privkey_tweak_add ...\n");

  // NULL context
  memcpy(nonce1, priv1, 32);
  buffer_clear(nonce2, 32);
  nonce2[31] = 0x01;          // tweak = 1
  return_value = secp256k1_ec_privkey_tweak_add(NULL,nonce1,nonce2);
  assert(return_value == 1);                // tweak successful
  assert(call_back_data == 0);              // call back was never called
  assert(buffer_equals(nonce1, priv1, 31)); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // NULL output buffer
  memcpy(nonce1, priv1, 32);
  buffer_clear(nonce2, 32);
  nonce2[31] = 0x01;          // tweak = 1
  return_value = secp256k1_ec_privkey_tweak_add(ctx, NULL, nonce2);
  assert(return_value == 0);                // tweak failed
  assert(call_back_data == 42);             // error
  call_back_data = 0;
  
  // NULL input buffer
  memcpy(nonce1, priv1, 32);
  buffer_clear(nonce2, 32);
  nonce2[31] = 0x01;          // tweak = 1
  return_value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, NULL);
  assert(return_value == 0);                // tweak failed
  assert(call_back_data == 42);             // error
  call_back_data = 0;
     
  // adding tweak of 0
  memcpy(nonce1, priv1, 32);
  buffer_clear(nonce2, 32);
  return_value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(return_value == 1);                // tweak successful
  assert(call_back_data == 0);              // call back was never called
  assert(buffer_equals(nonce1, priv1, 32)); // 0 tweak has no impact

  // adding tweak of 1
  memcpy(nonce1, priv1, 32);
  buffer_clear(nonce2, 32);
  nonce2[31] = 0x01;
  return_value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(return_value == 1);                // tweak successful
  assert(call_back_data == 0);              // call back was never called
  assert(buffer_equals(nonce1, priv1, 31)); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // adding tweak of 1 to order_minus_one
  memcpy(nonce1, order_minus_one, 32);
  buffer_clear(nonce2, 32);
  nonce2[31] = 0x01;
  return_value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(return_value == 0);                // tweak failed
  assert(call_back_data == 0);              // but no error

  printf("\ntesting pubkey_tweak_add ...\n");

  const unsigned char* tweak = 
    "\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";

  // adding tweak to private key then retrieving public key -> pub
  memcpy(nonce1, priv1, 32);
  return_value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, tweak);
  assert(return_value == 1);
  return_value = secp256k1_ec_pubkey_create(ctx, &pub, nonce1);
  assert(return_value == 1);

  // adding tweak to public key -> pub2
  memcpy(&pub2, &pub1, 64);
  return_value = secp256k1_ec_pubkey_tweak_add(ctx, &pub2, tweak);
  assert(return_value == 1);

  // the two public keys are the same
 assert(buffer_equals(&pub, &pub2, 64));



  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);

}


