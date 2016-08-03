/* Globbing filename patterns with popen() */
#include<ctype.h>
#include<limits.h>
#include"print_wait_status.h" /* For printWaitStatus() */
#include"tlpi_hdr.h"

#define POPEN_FMT "/bin/ls -d %s 2> /dev/null"
#define PAT_SIZE 50
#define PCMD_BUF_SIZE (sizeof(POPEN_FMT) + PAT_SIZE)

int
main(int argc, char *argv[])
{
  char pat[PAT_SIZE];           /* pattern for globing */
  char popenCmd[PCMD_BUF_SIZE];
  FILE *fp;                     /* file stream returned by popen */
  Boolean badPattern;           /* Invalid characters in 'pat'? */

  int len, status, fileCnt, j;
  char pathname[PATH_MAX];
