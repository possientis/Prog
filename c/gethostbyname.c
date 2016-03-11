#include <netdb.h>
#include <sys/socket.h>
#include <stdio.h>


int main(){

  printf("ip = %lx\n",gethostbyname("localhost"));

  return 0;
}
