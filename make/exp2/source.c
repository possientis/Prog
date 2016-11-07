#if HAVE_CONFIG_H
# include <config.h>
#endif

#if HAVE_DLFCN_H
# include <dlfcn.h>
#else
# error Sorry, this code requires dlfcn.h.
#endif

#if HAVE_DLFCN_H
  handle = dlopen("/usr/lib/libwhatever.so", RTLD_NOW);
#endif
