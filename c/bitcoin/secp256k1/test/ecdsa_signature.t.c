#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "secp256k1.h"
#include "test.h"

static int test_ecdsa_signature_parse_compact();
static int test_ecdsa_signature_serialize_compact();
static int test_ecdsa_signature_parse_der();
static int test_ecdsa_signature_serialize_der();

int test_ecdsa_signature()
{
  assert(test_ecdsa_signature_parse_compact() == 0);
  assert(test_ecdsa_signature_serialize_compact() == 0);
  assert(test_ecdsa_signature_parse_der() == 0);
  assert(test_ecdsa_signature_serialize_der() == 0);

  return 0;
}

static int test_ecdsa_signature_parse_compact(){

  secp256k1_ecdsa_signature sig;  // 64 bytes

  int value;

  assert(sizeof(sig) == 64);

  fprintf(stderr,"\ntesting parsing signature (compact)...\n");
  
  // NULL context
  callback_data.in = "signature_parse_compact.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_compact(NULL, &sig, sig_bytes1); 
  assert(value == 1);               // parsing succeeded
  assert(callback_data.out == 0);   // no error

  // NULL output pointer
  callback_data.in = "signature_parse_compact.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_compact(ctx, NULL, sig_bytes1); 
  assert(value == 0);               // parsing failed
  assert(callback_data.out == 42);  // data returned from callback 

  // NULL input pointer
  callback_data.in = "signature_parse_compact.2";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig, NULL); 
  assert(value == 0);               // parsing failed
  assert(callback_data.out == 42);  // data returned from callback 


  // normal call
  callback_data.in = "signature_parse_compact.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig, sig_bytes1); 
  assert(value == 1);               // parsing succeeded
  assert(callback_data.out == 0);   // no error


  return 0;
}

static int test_ecdsa_signature_serialize_compact(){
  
  secp256k1_ecdsa_signature sig1; // signature to be serialized 
  unsigned char buffer[64];       // buffer to accomodate result of serialization
  int value;


  // setting up signature to be serialized
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1); 

  fprintf(stderr,"\ntesting serializing signature (compact)...\n");

  // NULL context
  memset(buffer,0x00, 64);        
  callback_data.in = "signature_serialize_compact.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_compact(NULL,buffer,&sig1);
  assert(value == 1);                           // serialization succeeded
  assert(memcmp(buffer,sig_bytes1,64) == 0);    // serialization is correct
  assert(callback_data.out == 0);               // no error
  
  // NULL output buffer
  memset(buffer,0x00, 64);        
  callback_data.in = "signature_serialize_compact.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,NULL,&sig1);
  assert(value == 0);                           // serialization failed
  assert(callback_data.out == 42);              // callback return value


  return 0;
}

static int test_ecdsa_signature_parse_der(){return 0;}
static int test_ecdsa_signature_serialize_der(){return 0;}



