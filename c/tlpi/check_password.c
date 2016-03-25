// need to compile with option -lcrypt
// this program needs to be run by a priviledged user, so requires
// sudo or prior su etc. In order to make the program usable by
// unpriviledged user, you can set ownership of executable to root:
// > sudo chown root a.out
// and then set the user setuid flag:
// > sudo chmod u+s a.out
// This turns the executable into a setuid program, which means
// that the process running the executable file will have
// an effective uid equal to the uid of the owner of the file 
// (which we have set to root) and therefore be priviledged.
// so typically the process will have a real uid of 1000 (john),
// an effective uid of 0, a saved uid of 0 (copied from effective)
// and a filesystem uid (linux specific, usually follows effective 
// uid unless we explicitely change that) of 0. You can check that 
// by looking at the /proc/PID/status file.
//
//
#define _BSD_SOURCE     /* Get getpass() declaration from <unistd.h> */
#define _XOPEN_SOURCE   /* Get crypt() declaration from <unistd.h> */
#include <unistd.h>
#include <limits.h>
#include <pwd.h>
#include <shadow.h>
#include "tlpi_hdr.h"


int
main(int argc, char *argv[])
{
  char *username, *password, *encrypted, *p;
  struct passwd *pwd;
  struct spwd *spwd;
  Boolean authOk;
  size_t len;
  long lnmax;

  lnmax = sysconf(_SC_LOGIN_NAME_MAX);
  if (lnmax == -1)  /* If limit is indeterminate */
    lnmax = 256;    /* make a guess */

  username = malloc(lnmax);
  if (username == NULL)
    errExit("malloc");

  printf("Username: ");
  fflush(stdout);
  if (fgets(username, lnmax, stdin) == NULL)
    exit(EXIT_FAILURE); /* Exit on EOF */

  len = strlen(username);
  if (username[len - 1] == '\n')
    username[len - 1] = '\0';     /* Remove trailing '\n' */


  pwd = getpwnam(username);
  if (pwd == NULL)
    fatal("couldn't get password record");
  spwd = getspnam(username);
  if (spwd == NULL && errno == EACCES)
    fatal("no permission to read shadow password file");

  if (spwd != NULL)     /* If there is a shadow password record */
    pwd->pw_passwd = spwd->sp_pwdp; /* Use the shadow password */

  password = getpass("Password: ");

  /* Encrypt password and erase cleartext version immediately */
  encrypted = crypt(password, pwd->pw_passwd);
  for (p = password; *p != '\0'; )
    *p++ = '\0';

  if (encrypted == NULL)
    errExit("crypt");

  authOk = strcmp(encrypted, pwd->pw_passwd) == 0;
  if (!authOk) {
    printf("Incorrect password\n");
    exit(EXIT_FAILURE);
  }

  printf("Successfully authenticated: UID=%ld\n", (long) pwd->pw_uid);

  /* Now do authenticated work... */
  exit(EXIT_SUCCESS);
}





