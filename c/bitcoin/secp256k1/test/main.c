#include <assert.h>
#include <stdio.h>
#include <string.h>

#include <secp256k1.h>
#include "test.h"


extern int test_macro();
extern int test_context();
extern int test_callback();
extern int test_pubkey();


int main()
{
  assert(test_setup() == 0);
  assert(test_macro() == 0);
  assert(test_context() == 0);
  assert(test_callback() == 0);
  assert(test_pubkey() == 0);

  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
 
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_ecdsa_signature sig3;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(sig1) == 64);
  assert(sizeof(fun) == 8);




  int value;

  // secp256k1_ec_pubkey_parse


  // secp256k1_ec_pubkey_parse
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes4, 65); 
  assert(value == 1);  // public key is valid


  // secp256k1_ec_pubkey_parse
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes5, 65); 
  assert(value == 0);        // public key is invalid
//  assert(callback_data == 42);   // CALLBACK IS NOT CALLED (WRONG?)
  callback_data = 0;
  
  // secp256k1_ec_pubkey_parse (NULL context)
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes4, 65); 
  assert(value == 1);        // SUCCESSFUL DESPITE NULL CONTEXT
  assert(callback_data == 0);      // unaffected by call

  // secp256k1_ec_pubkey_parse (NULL secp256k1_pubkey pointer)
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes4, 65); 
  assert(value == 0);    // failing call
  assert(callback_data == 42); // call back return value
  callback_data = 0;           // make sure next error correctly sets it

  // secp256k1_ec_pubkey_parse (NULL context)
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(value == 0);    // failing call
  assert(callback_data == 42); // call back return value
  callback_data = 0;           // make sure next error correctly sets it


  // pub1 and pub4 should parse into the same key
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  assert(value == 1);
  value = secp256k1_ec_pubkey_parse(ctx, &pub2, pubkey_bytes4, 65);
  assert(value == 1);
  assert(memcmp(&pub1, &pub2, sizeof(secp256k1_pubkey)) == 0);


  fprintf(stderr,"\ntesting serializing public key...\n");

  unsigned char buffer[65];
  size_t size = 65;

  // compressed
  fprintf(stderr,"compressed format...\n");
  // serializing with output buffer too small
  size = 32;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(value == 0);        // serialization failed (WRONG DOCUMENTATION) 
  assert(size == 32);               // size unchanged here
  assert(is_all_null(buffer, 65));  // output buffer unaffected 
  assert(callback_data == 42);     // call back return value
  callback_data = 0;               // make sure next error correctly sets it

  // NULL context
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      NULL, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(value == 1);                  // serialization succeeded
  assert(size == 33);                         // expecting 33 bytes written
  assert(memcmp(buffer, pubkey_bytes1, 33) == 0);  // success despite NULL context
  assert(callback_data == 0);                // unaffected by call

  // NULL output buffer
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, NULL, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer, 65));  // output buffer unaffected
  assert(callback_data == 42);     // call back return value
  callback_data = 0;               // make sure next error correctly sets it

  // NULL input pubkey pointer
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, NULL, SECP256K1_EC_COMPRESSED
  );
  assert(value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer, 65));  // output buffer unaffected
  assert(callback_data == 42);     // call back return value
  callback_data = 0;               // make sure next error correctly sets it


  // secp256k1_ec_pubkey_serialize
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_COMPRESSED
  );
  assert(value == 1);        // should always be the case
  assert(size == 33);               // expecting 33 bytes written
  assert(memcmp(buffer, pubkey_bytes1, 33) == 0);
  assert(callback_data == 0);      // unaffected by call

  // uncompressed
  fprintf(stderr,"uncompressed format...\n");
  
  // serializing with output buffer too small
  size = 64;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(value == 0);    // should always be the case
  assert(size == 64);           // size unchanged here
  assert(is_all_null(buffer, 65));  // output buffer unaffected
  assert(callback_data == 42); // call back return value
  callback_data = 0;           // make sure next error correctly sets it

  // NULL context
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      NULL, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(value == 1);                  // serialization succeeded
  assert(size == 65);                         // expecting 33 bytes written
  assert(memcmp(buffer, pubkey_bytes4, 65) == 0);  // success despite NULL context
  assert(callback_data == 0);                // unaffected by call

  // NULL output buffer
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, NULL, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer, 65));  // output buffer unaffected
  assert(callback_data == 42);     // call back return value
  callback_data = 0;               // make sure next error correctly sets it

  // NULL input pubkey pointer
  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, NULL, SECP256K1_EC_UNCOMPRESSED
  );
  assert(value == 0);        // serialization failed (WRONG DOCUMENTATION)
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer, 65));  // output buffer unaffected
  assert(callback_data == 42);     // call back return value
  callback_data = 0;               // make sure next error correctly sets it


  size = 65;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(
      ctx, buffer, &size, &pub1, SECP256K1_EC_UNCOMPRESSED
  );
  assert(value == 1);        // should always be the case
  assert(size == 65);               // expecting 33 bytes written
  assert(memcmp(buffer, pubkey_bytes4, 65) == 0);
  assert(callback_data == 0);      // unaffected by call


  fprintf(stderr,"\ntesting parsing signature (compact)...\n");

  const unsigned char* sig_pubkey_bytes1 = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\x0e\x5c\x6e\xc6\x54\x08\xd6\x5a\xae\x9e\x1c\xe8\xe9\x53\xc3\x1e"
    "\xd0\x3f\x41\x79\x09\x1d\x20\xd1\x59\xda\xe4\x19\xe9\x0c\xa3\x63";

  // NULL context (still works)
  value = secp256k1_ecdsa_signature_parse_compact(NULL, &sig1, sig_pubkey_bytes1); 
  assert(value == 1);      // parsing succeeded
  assert(callback_data == 0);    // unaffected by call

  // NULL output pointer
  value = secp256k1_ecdsa_signature_parse_compact(ctx, NULL, sig_pubkey_bytes1);  
  assert(value == 0);      // parsing failed
  assert(callback_data == 42);   // callback return value
  callback_data = 0;             // make sure next error correctly sets it


  // NULL input pointer
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, NULL);  
  assert(value == 0);      // parsing failed
  assert(callback_data == 42);   // callback return value
  callback_data = 0;             // make sure next error correctly sets it
  
  // secp256k1_ecdsa_signature_parse_compact
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_pubkey_bytes1);  
  assert(value == 1);      // parsing succeeded
  assert(callback_data == 0);    // unaffected by call
  

  fprintf(stderr,"\ntesting serializing signature (DER)...\n");
  unsigned char der[128];
  
  // NULL context
  size = 128;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(NULL,der,&size,&sig1); 
  assert(value == 1);      // serialization succeeded
  assert(size == 71);             // der serialization is 71 bytes in this case
  assert(callback_data == 0);    // unaffected by call

  // NULL output pointer
  size = 128;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(ctx,NULL,&size,&sig1); 
  assert(value == 0);      // serialization failed
  assert(size == 128);            // size unchanged
  assert(is_all_null(der, 128));  // output buffer unaffected
  assert(callback_data == 42);   // check callback return value
  callback_data = 0;             // make sure next error correctly sets it
  
  // output pointer only 71 bytes
  size = 71;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(value == 1);      // serialization succeeded
  assert(size == 71);
  assert(callback_data == 0);    // unaffected by call

  // output pointer only 70 bytes (CALLBACK not being called)
  size = 70;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(value == 0);      // can't serialize
  assert(size == 71);             // size is changed here 
  assert(is_all_null(der, 128));  // output buffer unaffected
  assert(callback_data == 0);    // CALLBACK IS NOT CALLED ! (WRONG)
  callback_data = 0;             // make sure next error correctly sets it

  // null input pointer
  size = 128;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,NULL); 
  assert(value == 0);      // can't serialize
  assert(size == 128);            // size is unchanged
  assert(is_all_null(der, 128));  // output buffer unaffected
  assert(callback_data == 42);   // checking callback return value
  callback_data = 0;             // make sure next error correctly sets it

  // secp256k1_ecdsa_signature_serialize_der
  size = 128;
  memset(der,0x00, 128);
  value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(value == 1);
  assert(size == 71);
  assert(callback_data == 0);    // unaffected by call
 

  fprintf(stderr,"\ntesting parsing signature (DER)...\n");

  // NULL context 
  size = 71;
  value = secp256k1_ecdsa_signature_parse_der(NULL,&sig,der,size); 
  assert(value == 1);      // parsing was succesful
  assert(memcmp(&sig1, &sig, sizeof(secp256k1_ecdsa_signature)) == 0);

  // NULL input pointer
  size = 71;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,NULL,size); 
  assert(value == 0);      // can't parse
  assert(callback_data == 42); 
  callback_data = 0;             // make sure next error correctly sets it

  // NULL output pointer
  size = 71;
  value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(value == 0);      // can't parse
  assert(callback_data == 42);    
  callback_data = 0;             // make sure next error correctly sets it

  // wrong size input
  size = 70;
  value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der,size); 
  assert(value == 0);      // can't parse
  assert(size == 70);             // size unchanged
  assert(callback_data == 42);    
  callback_data = 0;             // make sure next error correctly sets it

  // secp256k1_ecdsa_signature_parse_der
  size = 71;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig2,der,size); 
  assert(value == 1);      // parsing was succesful
  assert(memcmp(&sig1, &sig2, sizeof(secp256k1_ecdsa_signature)) == 0);

  fprintf(stderr,"\ntesting serializing signature (compact)...\n");

  unsigned char buffer64[64];

  // NULL context
  memset(buffer64,0x00, 64);
  value = secp256k1_ecdsa_signature_serialize_compact(NULL,buffer64,&sig1);
  assert(value ==1);                       // serialization succeeded
  assert(memcmp(buffer64,sig_pubkey_bytes1,64) == 0);  // initial signature
  assert(callback_data == 0);

  // NULL output buffer
  memset(buffer64,0x00, 64);
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,NULL,&sig1);
  assert(value ==0);                       // serialization failed
  assert(callback_data == 42);
  callback_data = 0;

  // NULL input signature pointer
  memset(buffer64,0x00, 64);
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer64,NULL);
  assert(value ==0);                       // serialization failed
  assert(callback_data == 42);
  callback_data = 0;

  
  // secp2561_ecdsa_signature_serialize_compact
  memset(buffer64,0x00, 64);
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer64,&sig1);
  assert(value ==1);                       // serialization succeeded
  assert(memcmp(buffer64,sig_pubkey_bytes1,64) == 0);  // initial signature
  assert(callback_data == 0);

  fprintf(stderr,"\ntesting verifying signature...\n");
  
  const unsigned char *hash1 = 
    "\x7f\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d"
    "\xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69";

  const unsigned char *hash2 =  /* typo in first byte */
    "\xff\x83\xb1\x65\x7f\xf1\xfc\x53\xb9\x2d\xc1\x81\x48\xa1\xd6\x5d"
    "\xfc\x2d\x4b\x1f\xa3\xd6\x77\x28\x4a\xdd\xd2\x00\x12\x6d\x90\x69";

  // NULL context (segmentation fault)
//  value = secp256k1_ecdsa_verify(NULL, &sig1, hash1, &pub1); 
//  assert(value == 1);
 // assert(callback_data == 0);

  // NULL signature pointer
  value = secp256k1_ecdsa_verify(ctx, NULL, hash1, &pub1); 
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL msg32 pointer
  value = secp256k1_ecdsa_verify(ctx, &sig1, NULL, &pub1); 
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL pubkey pointer
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, NULL); 
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // wrong message
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash2, &pub1); 
  assert(value == 0);    // verification failes
  assert(callback_data == 0);  // but this is not an error, callback not called

  // wrong pubkey
  value = secp256k1_ec_pubkey_parse(ctx,&pub2, pubkey_bytes6, 33);
  assert(value == 1);
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub2); 
  assert(value == 0);    // verification fails
  assert(callback_data == 0);  // but not an error

  // secp256k1_ecdsa_verify
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub1); 
  assert(value == 1);
  assert(callback_data == 0);

  fprintf(stderr,"\ntesting normalizing signature...\n");


  // non-normalized counterpart of sig_pubkey_bytes1
  const unsigned char* sig_pubkey_bytes2 = 
    "\x98\x62\x10\xb9\xdc\x0a\x2f\x21\xbc\xae\xc0\x96\xf4\xf5\x5f\xf4"
    "\x48\x6f\xcc\x4e\x3a\xaf\xe7\xe0\xcb\xf6\x46\x92\x59\x6e\x99\x4a"
    "\xf1\xa3\x91\x39\xab\xf7\x29\xa5\x51\x61\xe3\x17\x16\xac\x3c\xdf"
    "\xea\x6f\x9b\x6d\xa6\x2b\x7f\x6a\x65\xf7\x7a\x72\xe7\x29\x9d\xde";

  // parsing key
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_pubkey_bytes2);
  assert(value == 1);  // parsing successful 

  // key not normalized, hence signature verification should fail
  value = secp256k1_ecdsa_verify(ctx, &sig2, hash1, &pub1);
  assert(value == 0);  // verification fails 

  // normalizing sig2
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized
  assert(memcmp(&sig1, &sig3, 64) == 0);    // sig1 == sig3

  // normalizing sig1
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig1);
  assert(value == 0);                  // sig1 was already normalized

  // NULL context
  value = secp256k1_ecdsa_signature_normalize(NULL, &sig3, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized

  // NULL ouput (only testing sig2 for normality)
  value = secp256k1_ecdsa_signature_normalize(ctx, NULL, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized

  // NULL input
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, NULL);
  assert(value == 0);                  // not meaningful
  assert(callback_data == 42);
  callback_data = 0;



  fprintf(stderr,"\ntesting rfc6979 nonce function...\n");

  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;

  unsigned char nonce1[32];
  unsigned char nonce2[32];

  memset(nonce1,0x00, 32);
  memset(nonce2,0x00, 32);

  value = f1(nonce1, hash1, hash2, NULL, NULL, 0);
  assert(value == 1);

  value = f2(nonce2, hash1, hash2, NULL, NULL, 0);
  assert(value == 1);

  assert(memcmp(nonce1, nonce2, 32) == 0);

  // private key from Mastering Bitcoin
  const unsigned char* priv1 =
    "\x1e\x99\x42\x3a\x4e\xd2\x76\x08\xa1\x5a\x26\x16\xa2\xb0\xe9\xe5"
    "\x2c\xed\x33\x0a\xc5\x30\xed\xcc\x32\xc8\xff\xc6\xa5\x26\xae\xdd";

  value = f1(nonce1, hash1, priv1, NULL, NULL, 0); 
  assert(value == 1);

  value = f2(nonce2, hash1, priv1, NULL, NULL, 0); 
  assert(value == 1);
 
  // see java EC_Test_Utils.getDeterministicKey and Test18.java
  const unsigned char* nonce = 
    "\x8b\x87\x1e\x0f\x28\x6b\x37\x91\xab\xb6\xe1\xd7\xc2\x8e\x6c\x7e"
    "\x07\x19\x82\x9e\xfc\x03\xf6\x09\x4f\x70\xda\xb1\xb0\xf0\x0e\xfb";

  assert(memcmp(nonce1, nonce, 32) == 0);
  assert(memcmp(nonce2, nonce, 32) == 0);

  // NULL output pointer (segmentation fault: WRONG?)
  // value = f1(NULL, hash1, priv1, NULL, NULL, 0); 

  // NULL message pointer (segmentation fault: WRONG?)
  // value = f1(nonce1, NULL, priv1, NULL, NULL, 0); 

  // NULL key pointer (segmentation fault: WRONG?)
  // value = f1(nonce1, hash1, NULL, NULL, NULL, 0); 

  fprintf(stderr,"\ntesting ecdsa signature generation...\n");

  // NULL context: segmentation fault
//  value = secp256k1_ecdsa_sign(NULL, &sig, hash1, priv1, f1, NULL);

  // NULL output pointer
  value = secp256k1_ecdsa_sign(ctx, NULL, hash1, priv1, f1, NULL);
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL message pointer
  value = secp256k1_ecdsa_sign(ctx, &sig, NULL, priv1, f1, NULL);
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL priv1ate key pointer
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, NULL, f1, NULL);
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL nonce function pointer
  memset(&sig,0x00, 64);
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, NULL, NULL);
  assert(value == 1);  // signing successful (default nonce is used)
  assert(memcmp(&sig,&sig1,64) == 0);
  assert(callback_data == 0);

  // secp256k1_ecdsa_sign
  memset(&sig,0x00, 64);
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, f1, NULL);
  assert(value == 1);
  assert(memcmp(&sig,&sig1,64) == 0);
  assert(callback_data == 0);

  fprintf(stderr,"\ntesting veryfying secret keys...\n");

  const unsigned char* order = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";
  
  // curve order is not a valid private key
  value = secp256k1_ec_seckey_verify(ctx, order);
  assert(value == 0);
  assert(callback_data == 0);

  const unsigned char* order_minus_one = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x40";

  // curve order less one is a valid private key
  value = secp256k1_ec_seckey_verify(ctx, order_minus_one);
  assert(value == 1);
  assert(callback_data == 0);

  // zero is not a valid private key
  memset(nonce1,0x00, 32);
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 0);
  assert(callback_data == 0);

  // one is a valid private key
  memset(nonce1,0x00, 32);
  nonce1[31] = 0x01;
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 1);
  assert(callback_data == 0);

  // 2^32 -1 is not a valid private key
  int i;
  for(i = 0; i < 32; ++i)
    nonce1[i] = 0xff;
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 0);
  assert(callback_data == 0);

  // NULL context
  value = secp256k1_ec_seckey_verify(NULL, priv1);
  assert(value == 1);
  assert(callback_data == 0);

  // Mastering Bitcoin private key is valid
  value = secp256k1_ec_seckey_verify(ctx, priv1);
  assert(value == 1);
  assert(callback_data == 0);

 
  fprintf(stderr,"\ntesting public key creation from private key...\n");

  // NULL context: segmentation fault
//  value = secp256k1_ec_pubkey_create(NULL, &pub, priv1);

  // NULL output buffer
  value = secp256k1_ec_pubkey_create(ctx, NULL, priv1);
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // NULL private key pointer
  value = secp256k1_ec_pubkey_create(ctx, &pub, NULL);
  assert(value == 0);
  assert(callback_data == 42);
  callback_data = 0;

  // invalid private key
  value = secp256k1_ec_pubkey_create(ctx, &pub, order);
  assert(value == 0);    // failure
  assert(callback_data == 0);  // but not an error

  // secp256k1_ec_pubkey_create
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, priv1);
  assert(value == 1);
  assert(callback_data == 0);
  assert(memcmp(&pub, &pub1, 64) == 0);

  fprintf(stderr,"\ntesting privkey_tweak_add...\n");

  // NULL context
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  value = secp256k1_ec_privkey_tweak_add(NULL,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // NULL output buffer
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  value = secp256k1_ec_privkey_tweak_add(ctx, NULL, nonce2);
  assert(value == 0);                // tweak failed
  assert(callback_data == 42);             // error
  callback_data = 0;
  
  // NULL input buffer
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, NULL);
  assert(value == 0);                // tweak failed
  assert(callback_data == 42);             // error
  callback_data = 0;
     
  // adding tweak of 0
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 32) == 0); // 0 tweak has no impact

  // adding tweak of 1
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // adding tweak of 1 to order_minus_one
  memcpy(nonce1, order_minus_one, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 0);                // tweak failed
  assert(callback_data == 0);              // but no error

  fprintf(stderr,"\ntesting pubkey_tweak_add...\n");

  const unsigned char* tweak = 
    "\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";

  // adding tweak to private key then retrieving public key -> pub
  memcpy(nonce1, priv1, 32);
  value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, tweak);
  assert(value == 1);
  value = secp256k1_ec_pubkey_create(ctx, &pub, nonce1);
  assert(value == 1);

  // adding tweak to public key -> pub2
  memcpy(&pub2, &pub1, 64);
  value = secp256k1_ec_pubkey_tweak_add(ctx, &pub2, tweak);
  assert(value == 1);

  // the two public keys are the same
  assert(memcmp(&pub, &pub2, 64) == 0);


  fprintf(stderr,"\ntesting privkey_tweak_mul...\n");
  
  // multiplying with tweak of 1
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak succeeds
  assert(callback_data == 0);              // no error
  assert(memcmp(nonce1, priv1, 32) == 0); // no impact

  // multiplying with tweak of 0
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 0);                // tweak fails
  assert(callback_data == 0);              // but no error

  // multiplying with tweak of 2
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 2;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak fails
  assert(callback_data == 0);              // but no error
  assert(nonce1[0] == (0x1e << 1) + 1);
 
  fprintf(stderr,"\ntesting pubkey_tweak_mul...\n");
  // not doing much here, don't understand this function yet
  // multiplying tweak to public key -> pub2
  memcpy(&pub2, &pub1, 64);
  value = secp256k1_ec_pubkey_tweak_mul(ctx, &pub2, tweak);
  assert(value == 1);


  fprintf(stderr,"\ntesting context_randomize...\n");
  value = secp256k1_context_randomize(ctx, priv1);
  assert(value == 1);

  fprintf(stderr,"\ntesting pubkey_combine...\n");
  // not doing much here
  memcpy(&pub2, &pub1, 64);
  const secp256k1_pubkey* const list[2] = { &pub1, &pub2 };
  value = secp256k1_ec_pubkey_combine(ctx, &pub, list, 2);
  assert(value == 1);
  
  // secp2561k1_context_destroy
  secp256k1_context_destroy(ctx);

  return 0;

}
