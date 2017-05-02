#include <assert.h>
#include <stdio.h>
#include <string.h>

#include <secp256k1.h>
#include "test.h"


extern int test_macro();
extern int test_context();
extern int test_callback();
extern int test_ec_pubkey();
extern int test_ecdsa_signature();


int main()
{
  assert(test_setup() == 0);
  assert(test_macro() == 0);
  assert(test_context() == 0);
  assert(test_callback() == 0);
  assert(test_ec_pubkey() == 0);
  assert(test_ecdsa_signature() == 0);

  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
 
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_ecdsa_signature sig3;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer

  assert(sizeof(fun) == 8);

  int value;

  unsigned char buffer[65];
  size_t size = 65;

  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);

 unsigned char der[128];
  
  // secp256k1_ecdsa_signature_serialize_der
  size = 128;
  memset(der,0x00, 128);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx,der,&size,&sig1); 
  assert(value == 1);
  assert(size == 71);
  assert(callback_data.out == 0);    // unaffected by call
 
  
  unsigned char buffer64[64];

  
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
 // assert(callback_data.out == 0);

  // NULL signature pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, NULL, hash1, &pub1); 
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL msg32 pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, NULL, &pub1); 
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL pubkey pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, NULL); 
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // wrong message
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash2, &pub1); 
  assert(value == 0);    // verification failes
  assert(callback_data.out == 0);  // but this is not an error, callback not called

  // wrong pubkey
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx,&pub2, pubkey_bytes6, 33);
  assert(value == 1);
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub2); 
  assert(value == 0);    // verification fails
  assert(callback_data.out == 0);  // but not an error

  // secp256k1_ecdsa_verify
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash1, &pub1); 
  assert(value == 1);
  assert(callback_data.out == 0);

  fprintf(stderr,"\ntesting normalizing signature...\n");


  // parsing key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);
  assert(value == 1);  // parsing successful 

  // key not normalized, hence signature verification should fail
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig2, hash1, &pub1);
  assert(value == 0);  // verification fails 

  // normalizing sig2
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized
  assert(memcmp(&sig1, &sig3, 64) == 0);    // sig1 == sig3

  // normalizing sig1
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, &sig1);
  assert(value == 0);                  // sig1 was already normalized

  // NULL context
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(NULL, &sig3, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized

  // NULL ouput (only testing sig2 for normality)
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, NULL, &sig2);
  assert(value == 1);                  // sig2 was *not* normalized

  // NULL input
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig3, NULL);
  assert(value == 0);                  // not meaningful
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;



  fprintf(stderr,"\ntesting rfc6979 nonce function...\n");

  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;

  unsigned char nonce1[32];
  unsigned char nonce2[32];

  memset(nonce1,0x00, 32);
  memset(nonce2,0x00, 32);

  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = f1(nonce1, hash1, hash2, NULL, NULL, 0);
  assert(value == 1);

  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = f2(nonce2, hash1, hash2, NULL, NULL, 0);
  assert(value == 1);

  assert(memcmp(nonce1, nonce2, 32) == 0);

  // private key from Mastering Bitcoin
  const unsigned char* priv1 =
    "\x1e\x99\x42\x3a\x4e\xd2\x76\x08\xa1\x5a\x26\x16\xa2\xb0\xe9\xe5"
    "\x2c\xed\x33\x0a\xc5\x30\xed\xcc\x32\xc8\xff\xc6\xa5\x26\xae\xdd";

  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = f1(nonce1, hash1, priv1, NULL, NULL, 0); 
  assert(value == 1);

  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
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
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_sign(ctx, NULL, hash1, priv1, f1, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL message pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_sign(ctx, &sig, NULL, priv1, f1, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL priv1ate key pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, NULL, f1, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL nonce function pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  memset(&sig,0x00, 64);
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, NULL, NULL);
  assert(value == 1);  // signing successful (default nonce is used)
  assert(memcmp(&sig,&sig1,64) == 0);
  assert(callback_data.out == 0);

  // secp256k1_ecdsa_sign
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  memset(&sig,0x00, 64);
  value = secp256k1_ecdsa_sign(ctx, &sig, hash1, priv1, f1, NULL);
  assert(value == 1);
  assert(memcmp(&sig,&sig1,64) == 0);
  assert(callback_data.out == 0);

  fprintf(stderr,"\ntesting veryfying secret keys...\n");

  const unsigned char* order = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";
  
  // curve order is not a valid private key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order);
  assert(value == 0);
  assert(callback_data.out == 0);

  const unsigned char* order_minus_one = 
    "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x40";

  // curve order less one is a valid private key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order_minus_one);
  assert(value == 1);
  assert(callback_data.out == 0);

  // zero is not a valid private key
  memset(nonce1,0x00, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 0);
  assert(callback_data.out == 0);

  // one is a valid private key
  memset(nonce1,0x00, 32);
  nonce1[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 1);
  assert(callback_data.out == 0);

  // 2^32 -1 is not a valid private key
  int i;
  for(i = 0; i < 32; ++i)
    nonce1[i] = 0xff;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, nonce1);
  assert(value == 0);
  assert(callback_data.out == 0);

  // NULL context
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(NULL, priv1);
  assert(value == 1);
  assert(callback_data.out == 0);

  // Mastering Bitcoin private key is valid
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, priv1);
  assert(value == 1);
  assert(callback_data.out == 0);

 
  fprintf(stderr,"\ntesting public key creation from private key...\n");

  // NULL context: segmentation fault
//  value = secp256k1_ec_pubkey_create(NULL, &pub, priv1);

  // NULL output buffer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_create(ctx, NULL, priv1);
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // NULL private key pointer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_create(ctx, &pub, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);
  callback_data.in = 0;
  callback_data.out = 0;

  // invalid private key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_create(ctx, &pub, order);
  assert(value == 0);    // failure
  assert(callback_data.out == 0);  // but not an error

  // secp256k1_ec_pubkey_create
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, priv1);
  assert(value == 1);
  assert(callback_data.out == 0);
  assert(memcmp(&pub, &pub1, 64) == 0);

  fprintf(stderr,"\ntesting privkey_tweak_add...\n");

  // NULL context
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(NULL,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // NULL output buffer
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx, NULL, nonce2);
  assert(value == 0);                // tweak failed
  assert(callback_data.out == 42);             // error
  callback_data.in = 0;
  callback_data.out = 0;
  
  // NULL input buffer
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, NULL);
  assert(value == 0);                // tweak failed
  assert(callback_data.out == 42);             // error
  callback_data.in = 0;
  callback_data.out = 0;
     
  // adding tweak of 0
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 32) == 0); // 0 tweak has no impact

  // adding tweak of 1
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv1[31] + 1);

  // adding tweak of 1 to order_minus_one
  memcpy(nonce1, order_minus_one, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 0);                // tweak failed
  assert(callback_data.out == 0);              // but no error

  fprintf(stderr,"\ntesting pubkey_tweak_add...\n");

  const unsigned char* tweak = 
    "\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe"
    "\xba\xae\xdc\xe6\xaf\x48\xa0\x3b\xbf\xd2\x5e\x8c\xd0\x36\x41\x41";

  // adding tweak to private key then retrieving public key -> pub
  memcpy(nonce1, priv1, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx, nonce1, tweak);
  assert(value == 1);
  value = secp256k1_ec_pubkey_create(ctx, &pub, nonce1);
  assert(value == 1);

  // adding tweak to public key -> pub2
  memcpy(&pub2, &pub1, 64);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_add(ctx, &pub2, tweak);
  assert(value == 1);

  // the two public keys are the same
  assert(memcmp(&pub, &pub2, 64) == 0);


  fprintf(stderr,"\ntesting privkey_tweak_mul...\n");
  
  // multiplying with tweak of 1
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak succeeds
  assert(callback_data.out == 0);              // no error
  assert(memcmp(nonce1, priv1, 32) == 0); // no impact

  // multiplying with tweak of 0
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 0);                // tweak fails
  assert(callback_data.out == 0);              // but no error

  // multiplying with tweak of 2
  memcpy(nonce1, priv1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 2;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak fails
  assert(callback_data.out == 0);              // but no error
  assert(nonce1[0] == (0x1e << 1) + 1);
 
  fprintf(stderr,"\ntesting pubkey_tweak_mul...\n");
  // not doing much here, don't understand this function yet
  // multiplying tweak to public key -> pub2
  memcpy(&pub2, &pub1, 64);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_mul(ctx, &pub2, tweak);
  assert(value == 1);


  fprintf(stderr,"\ntesting context_randomize...\n");
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_context_randomize(ctx, priv1);
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
