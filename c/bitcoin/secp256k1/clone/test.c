#include "include/secp256k1.h"

#include <assert.h>
#include <stdio.h>

int main() {

  // making sure cloned version of library is running
  assert(secp256k1_check_version() == 1);

  // trying out a few declarations
  
  // nonce_function
  secp256k1_nonce_function fun;
  assert(sizeof(fun) == 8);

  // context
  secp256k1_context *ctx;
  secp256k1_context *clone;
  assert(sizeof(ctx) == 8);
  assert(sizeof(clone) == 8);

  // pubkey
  secp256k1_pubkey pub;
  secp256k1_pubkey pub1;
  secp256k1_pubkey pub2;
  assert(sizeof(pub) == 64);
  assert(sizeof(pub1) == 64);
  assert(sizeof(pub2) == 64);

  // signature
  secp256k1_ecdsa_signature sig;
  secp256k1_ecdsa_signature sig1;
  secp256k1_ecdsa_signature sig2;
  secp256k1_ecdsa_signature sig3;
  assert(sizeof(sig) == 64);
  assert(sizeof(sig1) == 64);
  assert(sizeof(sig2) == 64);
  assert(sizeof(sig3) == 64);

  /**********************************************************************/
  /*                          nonce_function                            */
  /**********************************************************************/

  /**********************************************************************/
  /*                               context                              */
  /**********************************************************************/








  return 0;
}
