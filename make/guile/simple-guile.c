// gcc -o simple-guile simple-guile.c $(pkg-config --cflags --libs guile-2.2)
// For some reason, HOSTNAME needs to be exported first for my-hostname to work

#include <stdlib.h>
#include <libguile.h>

static SCM
my_hostname (void)
{
  char *s = getenv ("HOSTNAME");
  if (s == NULL)
    return SCM_BOOL_F;
  else
    return scm_from_locale_string (s);
}

static void
inner_main (void *data, int argc, char **argv)
{
  scm_c_define_gsubr ("my-hostname", 0, 0, 0, my_hostname);
  scm_shell (argc, argv);
}

int
main (int argc, char **argv)
{
  scm_boot_guile (argc, argv, inner_main, 0);
  return 0; /* never reached */
}


