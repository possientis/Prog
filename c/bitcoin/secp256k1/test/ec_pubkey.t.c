#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "secp256k1.h"
#include "test.h"

static int test_ec_pubkey_parse();
static int test_ec_pubkey_serialize(int);

int test_ec_pubkey()
{
  assert(test_ec_pubkey_parse() == 0);
  assert(test_ec_pubkey_serialize(SECP256K1_EC_COMPRESSED) == 0);
  assert(test_ec_pubkey_serialize(SECP256K1_EC_UNCOMPRESSED) == 0);

  return 0;

}

static int test_ec_pubkey_serialize(int flag)
{

  int value;
  unsigned char buffer[65];
  size_t size;
  secp256k1_pubkey pub1;

  // setting pubkey object to be serialized
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);

  // some parameters
  int compressed = (flag == SECP256K1_EC_COMPRESSED);
  const char* str = compressed ? "": "un";
  int expected_size = compressed ? 33 : 65;
  const unsigned char* bytes = compressed ? pubkey_bytes1 : pubkey_bytes4;
  

  fprintf(stderr,"\ntesting serializing public key (%scompressed) ...\n", str);

  // output buffer is too small
  size = expected_size - 1;
  callback_data.in = "pubkey_serialize.1";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(ctx, buffer, &size, &pub1, flag);
  assert(value == 0);               // serialization failed
  assert(size == expected_size - 1);// size unchanged here
  assert(is_all_null(buffer, 65));  // output buffer unaffected 
  assert(callback_data.out == 42);      // call back return value

  // NULL context
  size = 65;
  callback_data.in = "pubkey_serialize.0";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(NULL, buffer, &size, &pub1, flag);
  assert(value == 1);               // serialization succeeded
  assert(size == expected_size);    // 33 bytes written
  assert(memcmp(buffer, bytes, expected_size) == 0);
  assert(callback_data.out == 0);       // no error 

  // NULL output buffer
  size = 65;
  callback_data.in = "pubkey_serialize.2";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(ctx, NULL, &size, &pub1, flag);
  assert(value == 0);               // serialization failed
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer,65));   // output buffer unaffected
  assert(callback_data.out == 42);      // call back return value

  // NULL output buffer size pointer
  size = 65;
  callback_data.in = "pubkey_serialize.3";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(ctx, buffer, NULL, &pub1, flag);
  assert(value == 0);               // serialization failed
  assert(size == 65);               // size unaffected
  assert(is_all_null(buffer,65));   // output buffer unaffected
  assert(callback_data.out == 42);      // call back return value

  // NULL input pubkey pointer
  size = 65;
  callback_data.in = "pubkey_serialize.4";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(ctx, buffer, &size, NULL, flag);
  assert(value == 0);               // serialization failed
  assert(size == 0);                // 0 bytes written
  assert(is_all_null(buffer,65));   // output buffer unaffected
  assert(callback_data.out == 42);      // call back return value

  // normal call
  size = 65;
  callback_data.in = "pubkey_serialize.0";               
  callback_data.out = 0;
  memset(buffer,0x00, 65);
  value = secp256k1_ec_pubkey_serialize(ctx, buffer, &size, &pub1, flag);
  assert(value == 1);               // serialization succeeded
  assert(size == expected_size);    // 33 bytes written
  assert(memcmp(buffer, bytes, expected_size) == 0);
  assert(callback_data.out == 0);       // no error


  return 0;
}

static int test_ec_pubkey_parse()
{
  secp256k1_pubkey pub;
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;

  int value;

  assert(sizeof(pub) == 64);

  fprintf(stderr,"\ntesting parsing public key...\n");

  // secp256k1_ec_pubkey_parse
  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes1, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes2, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes3, 33); 
  assert(value == 0);         // public key is invalid
  assert(callback_data.out == 0); // but no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes4, 65); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes5, 65); 
  assert(value == 0);         // public key is invalid
  assert(callback_data.out == 0); // but no error 

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, pubkey_bytes6, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error 
  
  // NULL context
  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes1, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes2, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes3, 33); 
  assert(value == 0);         // public key is invalid
  assert(callback_data.out == 0); // but no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes4, 65); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes5, 65); 
  assert(value == 0);         // public key is invalid
  assert(callback_data.out == 0); // but no error 

  callback_data.in = "pubkey_parse.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(NULL, &pub, pubkey_bytes6, 33); 
  assert(value == 1);         // public key is valid
  assert(callback_data.out == 0); // no error 
 
  // NULL pubkey pointer
  callback_data.in = "pubkey_parse.1";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes1, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.2";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes2, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.3";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes3, 33); 
  assert(value == 0);         // invald call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.4";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes4, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.5";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes5, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.6";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, NULL, pubkey_bytes6, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback 
  
  // NULL bytes pointer
  callback_data.in = "pubkey_parse.7";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.8";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.9";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invald call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.10";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.11";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 65); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback

  callback_data.in = "pubkey_parse.12";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_parse(ctx, &pub, NULL, 33); 
  assert(value == 0);         // invalid call
  assert(callback_data.out == 42);// data returned from callback 

  // pubkey_bytes1 (compressed) and pubkey_bytes4 (uncompressed)
  // should be parsed into the same pubkey object
  value =  secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  value = secp256k1_ec_pubkey_parse(ctx, &pub2, pubkey_bytes4, 65);
  assert(memcmp(&pub1, &pub2, sizeof(secp256k1_pubkey)) == 0);

  return 0;
}


