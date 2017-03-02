#include <stdio.h>
#include <dlfcn.h>

int main()
{
  void *handle;
  void (*foo)(void);

  handle = dlopen("./libfoo.so", RTLD_NOW | RTLD_LOCAL);

  if(handle == NULL){
    printf("dlopen failed\n");
    return 1;
  }

  foo = (void (*)(void)) dlsym(handle, "foo");

  if(foo) foo();

  dlclose(handle);
}


