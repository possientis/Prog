#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <secp256k1.h>
#include "test.h"

static int test_ec_pubkey_parse();
static int test_ec_pubkey_serialize(int);
static int test_ec_pubkey_create();
static int test_ec_pubkey_tweak_add();
static int test_ec_pubkey_tweak_mul();
static int test_ec_pubkey_combine();


int test_ec_pubkey()
{
  assert(test_ec_pubkey_parse() == 0);
  assert(test_ec_pubkey_serialize(SECP256K1_EC_COMPRESSED) == 0);
  assert(test_ec_pubkey_serialize(SECP256K1_EC_UNCOMPRESSED) == 0);
  assert(test_ec_pubkey_create() == 0);
  assert(test_ec_pubkey_tweak_add() == 0);
  assert(test_ec_pubkey_tweak_mul() == 0);
  assert(test_ec_pubkey_combine() == 0);


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

static int test_ec_pubkey_create()
{

  secp256k1_pubkey pub, pub1;
  int value;

  // parsing public key used for comparison
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);

  fprintf(stderr,"\ntesting public key creation from private key...\n");

  // NULL context
  /* Segmentation fault 
  callback_data.in = "pubkey_create.0";
  callback_data.out = 0;
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(NULL, &pub, priv_bytes1);
  assert(value == 1);                   // creation succeeded
  assert(callback_data.out == 0);
  assert(memcmp(&pub, &pub1, 64) == 0); // checking correctness
  */

  // NULL output pointer
  callback_data.in = "pubkey_create.1";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_create(ctx, NULL, priv_bytes1);
  assert(value == 0);                   // creation failed
  assert(callback_data.out == 42);

  // NULL input pointer
  callback_data.in = "pubkey_create.2";
  callback_data.out = 0;
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, NULL);
  assert(value == 0);                   // creation failed
  assert(callback_data.out == 42);
  assert(is_all_null(&pub,64));


  // normal call
  callback_data.in = "pubkey_create.0";
  callback_data.out = 0;
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, priv_bytes1);
  assert(value == 1);                   // creation succeeded
  assert(callback_data.out == 0);
  assert(memcmp(&pub, &pub1, 64) == 0); // checking correctness

  // normal call (invalid seckey)
  callback_data.in = "pubkey_create.0";
  callback_data.out = 0;
  memset(&pub,0x00, 64);
  value = secp256k1_ec_pubkey_create(ctx, &pub, order_bytes);
  assert(value == 0);                   // creation failed
  assert(callback_data.out == 0);
  assert(is_all_null(&pub,64)); 



  return 0;
}

static int test_ec_pubkey_tweak_add()
{

  int value;
  secp256k1_pubkey pub, pub1, pub2;
  unsigned char priv[32];

  fprintf(stderr,"\ntesting pubkey_tweak_add...\n");

  // creating pubkey to which tweak will be added
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  assert(value == 1);

  // adding tweak to underlying private key
  memcpy(priv, priv_bytes1, 32);
  value = secp256k1_ec_privkey_tweak_add(ctx, priv, tweak_bytes);
  assert(value == 1);

  // creating pubkey corresponding to tweaked private key
  value = secp256k1_ec_pubkey_create(ctx, &pub2, priv);
  assert(value == 1);

  // adding a tweak to a public key, returns a public key which 
  // corresponds to the private key to which the tweak has been added
  
  /*
  // NULL context (segmentation fault)
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_add.0"; 
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_add(NULL, &pub, tweak_bytes);
  assert(value == 1);
  assert(memcmp(&pub, &pub2, 64) == 0);
  */

  // NULL output pointer
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_add.1"; 
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_add(ctx, NULL, tweak_bytes);
  assert(value == 0);
  assert(callback_data.out == 42);

  // NULL input pointer
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_add.2"; 
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_add(ctx, &pub, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);

  // normal call
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_add.0"; 
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_add(ctx, &pub, tweak_bytes);
  assert(value == 1);
  assert(memcmp(&pub, &pub2, 64) == 0);
  assert(callback_data.out == 0);


  return 0;
}

static int test_ec_pubkey_tweak_mul()
{
  int value;
  secp256k1_pubkey pub, pub1;
  unsigned char tweak[32];

  // parsing public key to be 'tweaked'
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);

  fprintf(stderr,"\ntesting pubkey_tweak_mul...\n");


  /*
  // NULL context (segmentation fault)
  memset(&tweak, 0, 32);
  tweak[31] = 0x01;
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_mul(NULL, &pub, tweak);
  assert(value == 1);
  assert(memcmp(&pub, &pub1, 64) == 0);
  */

  // NULL output pointer
  memset(&tweak, 0, 32);
  tweak[31] = 0x01;
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_mul.1";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_mul(ctx, NULL, tweak);
  assert(value == 0);
  assert(callback_data.out == 42);

  // NULL input pointer
  memset(&tweak, 0, 32);
  tweak[31] = 0x01;
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_mul.2";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_mul(ctx, &pub, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);


  // normal call (not checking much though as tweak = 1)
  memset(&tweak, 0, 32);
  tweak[31] = 0x01;
  memcpy(&pub, &pub1, 64);
  callback_data.in = "pubkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_tweak_mul(ctx, &pub, tweak);
  assert(value == 1);
  assert(callback_data.out == 0);
  assert(memcmp(&pub, &pub1, 64) == 0);

  return 0;
}

static int test_ec_pubkey_combine()
{

  int value;
  secp256k1_pubkey pub, pub1, pub2;

  fprintf(stderr,"\ntesting pubkey_combine...\n");

  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);

  // not doing much here
  memcpy(&pub2, &pub1, 64);
  const secp256k1_pubkey* const list[2] = { &pub1, &pub2 };
  callback_data.in = "pubkey_combine.0";
  callback_data.out = 0;
  value = secp256k1_ec_pubkey_combine(ctx, &pub, list, 2);
  assert(value == 1);
  assert(callback_data.out == 0);
 
  return 0;
}




