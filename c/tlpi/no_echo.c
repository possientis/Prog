/* Disabling terminal echoing */

#include <termios.h>
#include "tlpi_hdr.h"

#define BUF_SIZE 100

int
main(int argc, char *argv[])
{
  struct termios tp, save;
  char buf[BUF_SIZE];

  /* Retrieve current terminal settings, turn echoing off */

  if (tcgetattr(STDIN_FILENO, &tp) == -1)
    errExit("tcgetattr");
  save = tp;                /* So we can restore settings later */
  tp.c_lflag &= ~ECHO;      /* ECHO off, other bits unchanged */
  if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &tp) == -1)
    errExit("tcsetattr");

  /* Read some input and then display it back to the user */

  printf("Enter text: ");
  fflush(stdout);
  if (fgets(buf, BUF_SIZE, stdin) == NULL)
    printf("Got end-of-file/error on fgets()\n");
  else
    printf("\nRead: %s", buf);  

  /* Restore original terminal settings */

  if (tcsetattr(STDIN_FILENO, TCSANOW, &save) == -1)
    errExit("tcsetattr");

  exit(EXIT_SUCCESS);
}
