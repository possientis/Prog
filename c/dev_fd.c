#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

//stdout : another to writing to standard output
// also have /dev/fd/n , /dev/stdin, /dev/stdout, /dev/stderr
int main(){
  const char* buf = "Hello world";
  int fd = open("/dev/fd/1", O_WRONLY); // same as fd = dup(1);
  write(fd,buf,12);

  return 0; 

}
