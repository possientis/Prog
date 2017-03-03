#include <stdlib.h>
#include <stdio.h>
#include <dlfcn.h>


int main(int argc, char **argv) {
  void *handle;
  double (*cosine)(double);
  char *error;

  // using soname, not real name, not linker name
  handle = dlopen ("libm.so.6", RTLD_LAZY);

  if (!handle) {
    fputs (dlerror(), stderr);
    exit(1);
  }

  cosine = dlsym(handle, "cos");

  if ((error = dlerror()) != NULL) {
    fputs(error, stderr);
  exit(1);
  }

  printf ("cos(2) = %f\n", (*cosine)(2.0));
  dlclose(handle);

  return 0;
}
