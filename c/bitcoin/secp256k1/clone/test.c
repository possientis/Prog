#include <assert.h>
#include "include/secp256k1.h"

int main() {

  // making sure cloned version of library is running
  assert(secp256k1_check_version() == 1);

  return 0;
}
