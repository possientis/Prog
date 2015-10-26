#include <fcntl.h>

int main(){

  char buf[4096];
  int inf = open("/home/john/Prog/c/cp.c", O_RDONLY,0);
  int outf = open("/home/john/Prog/c/log",
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
