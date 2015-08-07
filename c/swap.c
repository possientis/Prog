#include<stdio.h>
#include<string.h>

void swap(void *p1, void* p2, int size){

  // dynamic allocation, some compilers may reject this
  char buffer[size];

  memcpy(buffer,p1,size);
  memcpy(p1,p2,size);
  memcpy(p2,buffer,size);


}



int main(int argc, char* argv[]){

  short a = 4;
  int b = 8;

  printf("a = %d\t b= %d\n",a,b);

  swap(&a,&b,4);

  printf("a = %d\t b= %d\n",a,b);

  return 0;

}


