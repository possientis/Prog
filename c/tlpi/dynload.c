/* Using the dlopen API */
/* gcc filename.c error_functions.c -ldl */

#include <dlfcn.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  void *libHandle;        /* Handle for shared library */
  void (*funcp)(void);    /* Pointer to function with no arguments */
  const char *err;


  if (argc != 3 || strcmp(argv[1], "--help") == 0)
    usageErr("%s lib-path func-name\n", argv[0]);

  /* Load the shared library and get a handle for later use */

  libHandle = dlopen(argv[1], RTLD_LAZY);
  if (libHandle == NULL)
    fatal("dlopen: %s", dlerror());

  /* Search library for symbol named in argv[2] */

  (void) dlerror();  /* Clear dlerror() */

  *(void **) (&funcp) = dlsym(libHandle, argv[2]);
  err = dlerror();
  if (err != NULL)
    fatal("dlsym: %s", err);

  /* If the address returned by dlsym() is non-NULL, try calling it
   * as a function that takes no arguments */

  if (funcp == NULL)
    printf("%s is NULL\n", argv[2]);
  else
    (*funcp)();

  dlclose(libHandle);  /* Close the library */

  exit(EXIT_SUCCESS);
}
