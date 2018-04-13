#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

sigjmp_buf buf;

void handler(int sig)
{
  siglongjmp(buf,1);
}

int main()
{
  signal(SIGINT, handler);

  if(!sigsetjmp(buf,1))
    printf("starting\n");
  else
    printf("\nrestarting\n");

  while(1)
  {
    sleep(1);
    printf("processing...\n");
  }

  printf("control flow should not reach this point\n");

  exit(0);

}
