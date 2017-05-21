#include <secp256k1.h>
#include <assert.h>
#include <stdio.h>

int main()
{
  printf("main is running...\n");
  secp256k1_context *ctx;
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
  assert(ctx);
  secp256k1_context_destroy(ctx);

  return 0;
}
