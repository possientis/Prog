#include <assert.h>
#include <stdio.h>
#include <string.h>

#include <secp256k1.h>
#include "test.h"



int main()
{
  assert(test_setup() == 0);
  assert(test_macro() == 0);
  assert(test_context() == 0);
  assert(test_callback() == 0);
  assert(test_ec_pubkey() == 0);
  assert(test_ecdsa_signature() == 0);
  assert(test_nonce_function() == 0);
  assert(test_ec_seckey() == 0);

  secp256k1_pubkey pub;           // 64 bytes
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
  secp256k1_ecdsa_signature sig;  // 64 bytes
  secp256k1_ecdsa_signature sig1;  // 64 bytes
  secp256k1_ecdsa_signature sig2;  // 64 bytes
  secp256k1_ecdsa_signature sig3;  // 64 bytes
  secp256k1_nonce_function fun;   // pointer


  int value;
  unsigned char buffer[65];
  size_t size = 65;
  unsigned char nonce1[32];
  unsigned char nonce2[32];

  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);
  const secp256k1_nonce_function f1 = secp256k1_nonce_function_rfc6979;
  const secp256k1_nonce_function f2 = secp256k1_nonce_function_default;


  fprintf(stderr,"\ntesting veryfying secret keys...\n");

 
  // curve order is not a valid private key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order_bytes);
  assert(value == 0);
  assert(callback_data.out == 0);


  // curve order less one is a valid private key
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order_minus_one_bytes);
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
  value = secp256k1_ec_seckey_verify(NULL, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);

  // Mastering Bitcoin private key is valid
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);

 
  fprintf(stderr,"\ntesting public key creation from private key...\n");

  // NULL context: segmentation fault
//  value = secp256k1_ec_pubkey_create(NULL, &pub, priv_bytes1);

  // NULL output buffer
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_create(ctx, NULL, priv_bytes1);
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
  value = secp256k1_ec_pubkey_create(ctx, &pub, order_bytes);
  assert(value == 0);    // failure
  assert(callback_data.out == 0);  // but not an error

  // secp256k1_ec_pubkey_create
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);
  assert(memcmp(&pub, &pub1, 64) == 0);

  fprintf(stderr,"\ntesting privkey_tweak_add...\n");

  // NULL context
  memcpy(nonce1, priv_bytes1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;          // tweak = 1
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(NULL,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv_bytes1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv_bytes1[31] + 1);

  // NULL output buffer
  memcpy(nonce1, priv_bytes1, 32);
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
  memcpy(nonce1, priv_bytes1, 32);
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
  memcpy(nonce1, priv_bytes1, 32);
  memset(nonce2,0x00, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv_bytes1, 32) == 0); // 0 tweak has no impact

  // adding tweak of 1
  memcpy(nonce1, priv_bytes1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak successful
  assert(callback_data.out == 0);              // call back was never called
  assert(memcmp(nonce1, priv_bytes1, 31) == 0); // tweak no impact on high order bytes
  assert(nonce1[31] == priv_bytes1[31] + 1);

  // adding tweak of 1 to order_minus_one_bytes
  memcpy(nonce1, order_minus_one_bytes, 32);
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
  memcpy(nonce1, priv_bytes1, 32);
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
  memcpy(nonce1, priv_bytes1, 32);
  memset(nonce2,0x00, 32);
  nonce2[31] = 0x01;
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 1);                // tweak succeeds
  assert(callback_data.out == 0);              // no error
  assert(memcmp(nonce1, priv_bytes1, 32) == 0); // no impact

  // multiplying with tweak of 0
  memcpy(nonce1, priv_bytes1, 32);
  memset(nonce2,0x00, 32);
  callback_data.in = 0;             // make sure next error correctly sets it
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,nonce1,nonce2);
  assert(value == 0);                // tweak fails
  assert(callback_data.out == 0);              // but no error

  // multiplying with tweak of 2
  memcpy(nonce1, priv_bytes1, 32);
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
  value = secp256k1_context_randomize(ctx, priv_bytes1);
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
