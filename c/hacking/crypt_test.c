#define _XOPEN_SOURCE /* get crypt() declaration from <unistd.h */
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
  if(argc < 2) {
    printf("Usage: %s <plaintext password> <salt value>\n", argv[0]);
    exit(1);
  }
  printf("password \"%s\" with salt \"%s\" ", argv[1], argv[2]);
  printf("hashes to ==> %s\n", crypt(argv[1], argv[2]));

  return 0;
}
