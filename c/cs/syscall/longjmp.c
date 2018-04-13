#include <setjmp.h>
#include <stdlib.h>
#include <stdio.h>

jmp_buf buf;

int error1 = 1;
int error2 = 0;

void foo();
void bar();


int main()
{
  int rc;

  rc = setjmp(buf);
  if(rc == 0)
    foo();
  else if (rc == 1)
    printf("Detected an error1 condition in foo\n");
  else if (rc == 2)
    printf("Detected an error2 condition in foo\n");
  else
    printf("Unknown error condition in foo\n");
  exit(0);
}


void foo()
{
  if(error1)
    longjmp(buf,1);
  bar();
}

void bar()
{
  if(error2)
    longjmp(buf,2);
}



