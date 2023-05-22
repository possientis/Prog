#include <fcntl.h>

int main(){

  char buf[4096];
  /* TODO: fix the ${HOME} issue if needed */
  int inf = open("${HOME}/Prog/c/cp.c", O_RDONLY,0);
  int outf = open("${HOME}/Prog/c/log",
      O_WRONLY|O_CREAT|O_TRUNC, 0600);

  int i = 0;

  do{
    i = read(inf,buf,4096);
    write(outf,buf,i);
  } while (i);


  close(outf);
  close(inf);

  return 0;
}
