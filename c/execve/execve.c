/* execve.c */
#include <stdio.h>
#include <stdlib.h>
#include<unistd.h>
#include<string>

int main(int argc, char* argv[])
{

  // initialization in two stages to avoid compiler warning
  char hello[] = "hello";
  char world[] = "world";
  char *newargv[4]={NULL,hello,world,NULL};
  char *newenviron[] ={NULL};

  if(argc != 2){
    fprintf(stderr, "Usage: %s <file-to-exec>\n",argv[0]);
    exit(EXIT_FAILURE);
  }

  newargv[0] = argv[1];

  execve(argv[1],newargv,newenviron);
  perror("execve"); /* execve() only returns on error */
  exit(EXIT_FAILURE);

}


