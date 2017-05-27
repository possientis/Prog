#include <assert.h>

#include "include/secp256k1.h"
#include "src/util.h"



int main() {

  assert(secp256k1_check() == 1);


  return 0;
}
