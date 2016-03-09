#include <sys/stat.h>
#include <fcntl.h>
#include <ctype.h>
#include "tlpi_hdr.h"

/* ./a.out file sleep &
 * ./a.out file
 * both processes will claim to have created file exclusively
 *
 * Need to use O_CREAT and O_EXCL and guarantee atomic execution
 * of checking whether file exists *and* actual creation.

int main(int argc, char* argv[]){

  int fd;

  fd = open(argv[1], O_WRONLY);
  /* Open 1: check if file exists */
  if (fd != -1) {
    /* Open succeeded */
    printf("[PID %ld] File \"%s\" already exists\n",
        (long) getpid(), argv[1]);
    close(fd);
  } else {
    if (errno != ENOENT) {
      /* Failed for unexpected reason */
      errExit("open");
    } else {
      /* window for failure */
      printf("[PID %ld] File \"%s\" doesn't exist yet\n", (long) getpid(), argv[1]);
      if (argc > 2) {
        /* Delay between check and create */
        sleep(5);
        /* Suspend execution for 5 seconds */
        printf("[PID %ld] Done sleeping\n", (long) getpid());
      }

      fd = open(argv[1], O_WRONLY | O_CREAT, S_IRUSR | S_IWUSR);
      if (fd == -1)
        errExit("open");
      printf("[PID %ld] Created file \"%s\" exclusively\n",
          (long) getpid(), argv[1]); /* MAY NOT BE TRUE! */
    }
  }

  return EXIT_SUCCESS;
}
