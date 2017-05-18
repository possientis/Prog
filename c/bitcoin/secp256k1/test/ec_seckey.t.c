#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "secp256k1.h"
#include "test.h"

static int test_ec_seckey_verify();
static int test_ec_privkey_tweak_add();
static int test_ec_privkey_tweak_mul();

static void times2(unsigned char* bytes, size_t size);

int test_ec_seckey()
{
  assert(test_ec_seckey_verify() == 0);
  assert(test_ec_privkey_tweak_add() == 0);
  assert(test_ec_privkey_tweak_mul() == 0);

  return 0;
}

static int test_ec_seckey_verify()
{

  int value;

  unsigned char seckey[32];

  fprintf(stderr,"\ntesting veryfying secret keys...\n");
  
  // NULL context 
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(NULL, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);

  // NULL input seckey pointer
  callback_data.in = "seckey_verify.1";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, NULL);
  assert(value == 0);
  assert(callback_data.out == 42);


  // normal call (Mastering Bitcoin private key is valid)
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, priv_bytes1);
  assert(value == 1);
  assert(callback_data.out == 0);

  // normal call (curve order is not valid)
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order_bytes);
  assert(value == 0);
  assert(callback_data.out == 0);

  // normal call (curve order - 1 is valid)
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, order_minus_one_bytes);
  assert(value == 1);
  assert(callback_data.out == 0);

  // normal call (zero is not valid)
  memset(seckey, 0x00, 32);
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, seckey);
  assert(value == 0);
  assert(callback_data.out == 0);

  // normal call (1 is valid)
  memset(seckey, 0x00, 32);
  seckey[31] = 0x01;
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, seckey);
  assert(value == 1);
  assert(callback_data.out == 0);

  // normal call (2^256 -1 is not valid)
  memset(seckey, 0xff, 32);
  callback_data.in = "seckey_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ec_seckey_verify(ctx, seckey);
  assert(value == 0);
  assert(callback_data.out == 0);


  return 0;
}

static int test_ec_privkey_tweak_add()
{

  int value;
  unsigned char seckey[32];
  unsigned char tweak[32];

  fprintf(stderr,"\ntesting privkey_tweak_add...\n");

  // NULL context (tweak of 1)
  memcpy(seckey, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;         // low order byte changed to 1 (big endian)
  callback_data.in = "privkey_tweak_add.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(NULL,seckey,tweak);
  assert(value == 1);
  assert(callback_data.out == 0);              
  assert(memcmp(seckey, priv_bytes1, 31) == 0); // equality 31 bytes only 
  assert(seckey[31] == priv_bytes1[31] + 1);    // cecking correctness

  // NULL output buffer (tweak of 1)
  memcpy(seckey, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;         // low order byte changed to 1 (big endian)
  callback_data.in = "privkey_tweak_add.1";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,NULL,tweak);
  assert(value == 0);
  assert(callback_data.out == 42);              // callback return value              
  // NULL input buffer (tweak of ...)
  memcpy(seckey, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;         // low order byte changed to 1 (big endian)
  callback_data.in = "privkey_tweak_add.2";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,seckey,NULL);
  assert(value == 0);
  assert(callback_data.out == 42);              // callback return value              
  // normal call (tweak of 0)
  memcpy(seckey, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  callback_data.in = "privkey_tweak_add.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,seckey,tweak);
  assert(value == 1);
  assert(callback_data.out == 0);              
  assert(memcmp(seckey, priv_bytes1, 32) == 0); // checking correctness

  // normal call (tweak of 1)
  memcpy(seckey, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;         // low order byte changed to 1 (big endian)
  callback_data.in = "privkey_tweak_add.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,seckey,tweak);
  assert(value == 1);
  assert(callback_data.out == 0);              
  assert(memcmp(seckey, priv_bytes1, 31) == 0); // equality 31 bytes only 
  assert(seckey[31] == priv_bytes1[31] + 1);    // cecking correctness

  // normal call (tweak of 1 added to order - 1)
  memcpy(seckey, order_minus_one_bytes, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;                 // low order byte changed to 1 (big endian)
  callback_data.in = "privkey_tweak_add.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_add(ctx,seckey,tweak);
  assert(value == 0);               // failure 
  assert(callback_data.out == 0);   // but no error            

  return 0;
}

static int test_ec_privkey_tweak_mul()
{
  fprintf(stderr,"\ntesting privkey_tweak_mul...\n");

  int value;
  unsigned char priv[32];
  unsigned char tweak[32];
  unsigned char check[32];

  // NULL context (tweak of 1)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;                 // low order byte set to 1 (big endian)
  callback_data.in = "privkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(NULL,priv,tweak);
  assert(value == 1);                
  assert(callback_data.out == 0);              
  assert(memcmp(priv, priv_bytes1, 32) == 0); // no impact

  // NULL output pointer (tweak of 1)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;                 // low order byte set to 1 (big endian)
  callback_data.in = "privkey_tweak_mul.1";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx, NULL,tweak);
  assert(value == 0);                
  assert(callback_data.out == 42);              

  // NULL input pointer (tweak of ...)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;                 // low order byte set to 1 (big endian)
  callback_data.in = "privkey_tweak_mul.1";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx, priv,NULL);
  assert(value == 0);                
  assert(callback_data.out == 42);              


  // normal call (tweak of 1)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  tweak[31] = 0x01;                 // low order byte set to 1 (big endian)
  callback_data.in = "privkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,priv,tweak);
  assert(value == 1);                
  assert(callback_data.out == 0);              
  assert(memcmp(priv, priv_bytes1, 32) == 0); // no impact

  // normal call (tweak of 0)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  callback_data.in = "privkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,priv,tweak);
  assert(value == 0);                         // tweak failed                
  assert(callback_data.out == 0);             // but no error 
  assert(is_all_null(priv,32));               // output altered despite error 

  // normal call (tweak of 2)
  memcpy(priv, priv_bytes1, 32);
  memset(tweak,0x00, 32);
  memcpy(check, priv_bytes1, 32);
  times2(check, 32);
  tweak[31] = 0x02;                 // low order byte set to 2 (big endian)
  callback_data.in = "privkey_tweak_mul.0";
  callback_data.out = 0;
  value = secp256k1_ec_privkey_tweak_mul(ctx,priv,tweak);
  assert(value == 1);                
  assert(callback_data.out == 0);              
  assert(priv[0] == (0x1e << 1) + 1); 
  assert(memcmp(priv,check,32) == 0);

  return 0;
}

static void times2(unsigned char * bytes, size_t size){
  int i;
  for(i = 0; i < size; ++i){
    bytes[i] = (bytes[i] << 1) % 256;
    if(i < size -1){
      if((bytes[i+1] << 1) > 256){
        bytes[i] +=1;
      }
    }
  }
}

