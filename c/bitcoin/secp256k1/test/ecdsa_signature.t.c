#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "secp256k1.h"
#include "test.h"

static int test_ecdsa_signature_parse_compact();
static int test_ecdsa_signature_serialize_compact();
static int test_ecdsa_signature_parse_der();
static int test_ecdsa_signature_serialize_der();
static int test_ecdsa_signature_verify();
static int test_ecdsa_signature_normalize();


int test_ecdsa_signature()
{
  assert(test_ecdsa_signature_parse_compact() == 0);
  assert(test_ecdsa_signature_serialize_compact() == 0);
  assert(test_ecdsa_signature_parse_der() == 0);
  assert(test_ecdsa_signature_serialize_der() == 0);
  assert(test_ecdsa_signature_verify() == 0);
  assert(test_ecdsa_signature_normalize() == 0);

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

  // NULL input signature pointer
  memset(buffer,0x00, 64);        
  callback_data.in = "signature_serialize_compact.2";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer,NULL);
  assert(value == 0);                           // serialization failed
  assert(is_all_null(buffer, 64));              // buffer unaffected
  assert(callback_data.out == 42);              // callback return value

  // normal call
  memset(buffer,0x00, 64);        
  callback_data.in = "signature_serialize_compact.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_compact(ctx,buffer,&sig1);
  assert(value == 1);                           // serialization succeeded
  assert(memcmp(buffer, sig_bytes1, 64) == 0);  // serialization is correct
  assert(callback_data.out == 0);               // no error


  return 0;
}

static int test_ecdsa_signature_parse_der(){

  secp256k1_ecdsa_signature sig, sig1;
  int value;
  size_t size;
  unsigned char der_bytes[71];  // bytes to be parsed

  // computing bytes to be parsed dynamically by serializing in DER 
  // format a signature obtained by parsing bytes in compact format.
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);
  value = secp256k1_ecdsa_signature_serialize_der(ctx, der_bytes, &size, &sig1); 
  assert(value == 1); assert(size == 71);

  assert(sizeof(sig) == 64);

  fprintf(stderr,"\ntesting parsing signature (DER)...\n");
  
  // NULL context 
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(NULL,&sig,der_bytes,71); 
  assert(value == 1);                   // parsing succeeded
  assert(memcmp(&sig1, &sig, 64) == 0); // parsing is correct
  assert(callback_data.out == 0);       // no error

  // NULL output pointer 
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(ctx,NULL,der_bytes,71); 
  assert(value == 0);                   // parsing failed
  assert(callback_data.out == 42);      // callback return value

  // NULL input buffer
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.2";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,NULL,71); 
  assert(value == 0);                   // parsing failed
  assert(callback_data.out == 42);      // callback return value

  // Wrong size input (70)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,der_bytes,70); 
  assert(value == 0);                   // parsing failed
  assert(callback_data.out == 0);       // but no error

  // Wrong size input (72) (possible buffer read overflow)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,der_bytes,72); 
  assert(value == 0);                   // parsing failed
  assert(callback_data.out == 0);       // but no error

  // normal call
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_parse_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_parse_der(ctx,&sig,der_bytes,71); 
  assert(value == 1);                   // parsing succeeded
  assert(memcmp(&sig1, &sig, 64) == 0); // parsing is correct
  assert(callback_data.out == 0);       // no error

  return 0;

}
static int test_ecdsa_signature_serialize_der(){
  
  secp256k1_ecdsa_signature sig1;       // signature to be serialized
  int value;
  size_t size;
  unsigned char buffer[128];            // der output buffer

  // parsing signature in compact format so it can be serialized in DER format
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);

  fprintf(stderr,"\ntesting serializing signature (DER)...\n");

  // NULL context
  size = 128;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(NULL,buffer,&size, &sig1); 
  assert(value == 1);                   // serialization succeeded
  assert(size == 71);                   // 71 bytes output in this case
  assert(callback_data.out == 0);       // no error

  // NULL output buffer
  size = 128;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, NULL,&size, &sig1); 
  assert(value == 0);                   // serialization failed
  assert(size == 128);                  // size argument unaffected
  assert(is_all_null(buffer, 128));     // buffer unaffected
  assert(callback_data.out == 42);      // callback return value

  // output buffer exactly 71 bytes
  size = 71;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, buffer,&size, &sig1); 
  assert(value == 1);                   // serialization succeeded
  assert(size == 71);                   // 71 bytes output
  assert(callback_data.out == 0);       //  no error

  // output buffer too small
  size = 70;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, buffer,&size, &sig1); 
  assert(value == 0);                   // serialization failed
  assert(size == 71);                   // size argument unaffected
  assert(is_all_null(buffer, 128));     // buffer unaffected
  assert(callback_data.out == 0);       // no error

  // NULL size pointer
  size = 128;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.2";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, buffer, NULL, &sig1); 
  assert(value == 0);                   // serialization failed
  assert(size == 128);                  // size argument unaffected
  assert(is_all_null(buffer, 128));     // buffer unaffected
  assert(callback_data.out == 42);      // callback return value

  // NULL signature pointer
  size = 128;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.3";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, buffer, &size, NULL); 
  assert(value == 0);                   // serialization failed
  assert(size == 128);                  // size argument unaffected
  assert(is_all_null(buffer, 128));     // buffer unaffected
  assert(callback_data.out == 42);      // callback return value
  
  // Normal call
  size = 128;
  memset(buffer,0x00, 128);
  callback_data.in = "signature_serialize_der.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_serialize_der(ctx, buffer, &size, &sig1); 
  assert(value == 1);                   // serialization failed
  assert(size == 71);                   // 71 bytes output
  assert(callback_data.out == 0);       //  no error

  return 0;
}

static int test_ecdsa_signature_verify(){

  int value;
  secp256k1_pubkey pub1, pub2, pub3;
  secp256k1_ecdsa_signature sig1, sig2, sig;

  // parsing key with which to successfully verify signature
  value = secp256k1_ec_pubkey_parse(ctx, &pub1, pubkey_bytes1, 33);
  // parsing key with which to unsuccessfully verify signature 
  value = secp256k1_ec_pubkey_parse(ctx, &pub2, pubkey_bytes2, 33);
  // parsing signature to be verified
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);
  // parsing non-normalized counterpart of sig1
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);

  fprintf(stderr,"\ntesting verifying signature...\n");
  
/* waiting for issue to be resolved before re-activating test
  // NULL context (segmentation fault)
  callback_data.in = "signature_verify.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(NULL, &sig1, hash_bytes1, &pub1); 
  assert(value == 0);
  assert(callback_data.out == 42);
*/

  // NULL signature pointer
  callback_data.in = "signature_verify.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, NULL, hash_bytes1, &pub1); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 42);  // callback return value

  // NULL hash pointer
  callback_data.in = "signature_verify.2";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, NULL, &pub1); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 42);  // callback return value

  // NULL public key pointer
  callback_data.in = "signature_verify.3";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes1, NULL); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 42);  // callback return value

  // 'null' valued public key
  memset(&pub3, 0x0, 64);
  callback_data.in = "signature_verify.4";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes1, &pub3); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 42);  // callback return value

  // invalid public key
  memset(&pub3, 0x01, 64);
  callback_data.in = "signature_verify.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes1, &pub3); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 0);   // but no error

  // wrong message
  callback_data.in = "signature_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes2, &pub1); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 0);   // but no error

  // wrong public key
  callback_data.in = "signature_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes1, &pub2); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 0);   // but no error

  // non-normalized signature
  callback_data.in = "signature_verify.0";             
  callback_data.out = 0;
  value = secp256k1_ecdsa_verify(ctx, &sig2, hash_bytes1, &pub1); 
  assert(value == 0);               // verification failed
  assert(callback_data.out == 0);   // but no error

  // normal call
  callback_data.in = "signature_verify.0";
  callback_data.out = 0;            
  value = secp256k1_ecdsa_verify(ctx, &sig1, hash_bytes1, &pub1); 
  assert(value == 1);               // verification succeeded
  assert(callback_data.out == 0);   // no error


  return 0;
} 

static int test_ecdsa_signature_normalize(){

  int value;
  secp256k1_ecdsa_signature sig1, sig2, sig;

  // sig2 is the non-normalized counterpart of sig1
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig1, sig_bytes1);
  value = secp256k1_ecdsa_signature_parse_compact(ctx, &sig2, sig_bytes2);

  fprintf(stderr,"\ntesting normalizing signature...\n");

  // NULL context (not normalized)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(NULL, &sig, &sig2);
  assert(value == 1);                     // signature was not normalized       
  assert(memcmp(&sig, &sig1, 64) == 0);   // normalization is correct
  assert(callback_data.out == 0);         // no error

  // NULL context (already normalized)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(NULL, &sig, &sig1);
  assert(value == 0);                     // signature was already normalized       
  assert(memcmp(&sig, &sig1, 64) == 0);   // normalization is correct
  assert(callback_data.out == 0);         // no error

  // NULL output pointer (not normalized)
  // This use of NULL pointer for output is permitted by API, the function
  // simply returns 1 (not normalized) or 0 (normalized) based on input.
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, NULL, &sig2);
  assert(value == 1);                     // signature was not normalized       
  assert(callback_data.out == 0);         // no error

  // NULL output pointer (already normalized)
  // This use of NULL pointer for output is permitted by API, the function
  // simply returns 1 (not normalized) or 0 (normalized) based on input.
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, NULL, &sig1);
  assert(value == 0);                     // signature was already normalized       
  assert(callback_data.out == 0);         // no error

   // NULL input pointer
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_normalize.1";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig, NULL);
  assert(value == 0);                     // well it returns here, why not      
  assert(callback_data.out == 42);        // backup return value


  // normal call (not normalized)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig, &sig2);
  assert(value == 1);                     // signature was not normalized       
  assert(memcmp(&sig, &sig1, 64) == 0);   // normalization is correct
  assert(callback_data.out == 0);         // no error

  // normal call (already normalized)
  memset(&sig, 0x00, 64);
  callback_data.in = "signature_normalize.0";
  callback_data.out = 0;
  value = secp256k1_ecdsa_signature_normalize(ctx, &sig, &sig1);
  assert(value == 0);                     // signature was already normalized       
  assert(memcmp(&sig, &sig1, 64) == 0);   // normalization is correct
  assert(callback_data.out == 0);         // no error


  return 0;
}



