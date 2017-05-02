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



