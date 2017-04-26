#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "secp256k1.h"
#include "test.h"

static int test_pubkey_parse();

int test_pubkey()
{
  assert(test_pubkey_parse() == 0);

  return 0;

}

int test_pubkey_parse()
{
  secp256k1_pubkey pub;
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;

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

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes4, 65); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes5, 65); 
  assert(value == 0);         // public key is invalid
  assert(callback_data == 0); // but no error 

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes6, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error 
  
  // NULL context
  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes1, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes2, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes3, 33); 
  assert(value == 0);         // public key is invalid
  assert(callback_data == 0); // but no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes4, 65); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes5, 65); 
  assert(value == 0);         // public key is invalid
  assert(callback_data == 0); // but no error 

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes6, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data == 0); // no error 
 
  // NULL pubkey pointer
  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes1, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes2, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes3, 33); 
  assert(value == 0);         // invald call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes4, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes5, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes6, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback 
  
  // NULL bytes pointer
  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invald call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback

  callback_data = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data == 42);// data returned from callback 

  // pubkey_bytes1 (compressed) and pubkey_bytes4 (uncompressed)
  // should be parsed into the same pubkey object
  value =  secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  value = secp256k1_ec_pubkey_parse(ctx, &pub2, pubkey_bytes4, 65);
  assert(memcmp(&pub1, &pub2, sizeof(secp256k1_pubkey)) == 0);

  return 0;
}


