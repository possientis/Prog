#include <stdio.h>

// compile with -Wnonnull option for warnings to be generated
void foo(void* p, void* q) __attribute__((nonnull(1,2)));
void bar(void* p, void* q) __attribute__((__nonnull__(1,2)));


int main()
{
  void* p = NULL;
  void* q = NULL;

  foo(NULL, q);     // warning
  foo(p, NULL);     // warning
  foo(NULL, NULL);  // warning x2
  foo(p, q);        // no warning

  bar(NULL,NULL);   // warning x2

  return 0;
}


void foo(void* p, void* q)
{
  printf("nonnull foo is running...\n");
}


void bar(void* p, void* q)
{
  printf("nonnull bar is running...\n");
}
