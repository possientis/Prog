#include <stdio.h>

int main(){
  char cmd[32];
  brk((void*)0x8051000);
  sprintf(cmd,"cat /proc/self/maps");
  system(cmd);
  return 0;
}
