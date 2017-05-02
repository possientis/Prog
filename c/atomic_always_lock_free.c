#include <stdio.h>
#include <assert.h>

#define TEST(type) do { \
  printf("__atomic_always_lock_free(sizeof(" #type ")) = %d (%d bytes)\n", \
      __atomic_always_lock_free(sizeof(type), NULL), sizeof(type)); \
  } while(0)


int main()
{

  TEST(char);
  TEST(short);
  TEST(int);
  TEST(long);
  TEST(void*);
  TEST(long long);

  return 0;
}
