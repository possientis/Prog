#include "hacking.h"

#include <string.h>
#include <malloc.h>
#include <stdlib.h>

void fatal(const char *message) {
  char error_message[100];
  strcpy(error_message, "[!!] Fatal Error ");
  strncat(error_message, message, 83);
  perror(error_message);
  exit(-1);
}

void *ec_malloc(unsigned int size) {
  void *ptr;
  ptr = malloc(size);
  if(ptr == NULL)
    fatal("in ec_malloc() on memory allocation");
  return ptr;
}

// Dumps raw memory in hex byte and printable split format
void dump(const unsigned char *data_buffer, unsigned int length) {
  unsigned char byte;
  unsigned int i, j;
  for(i=0; i < length; i++) {
    byte = data_buffer[i];
    printf("%02x ", data_buffer[i]); // Display byte in hex.
    if(((i%16)==15) || (i==length-1)) {
      for(j=0; j < 15-(i%16); j++)
        printf(" ");
      printf("| ");
      for(j=(i-(i%16)); j <= i; j++) { // Display printable bytes from line.
        byte = data_buffer[j];
        if((byte > 31) && (byte < 127)) // Inside printable char range
          printf("%c", byte);
        else
          printf(".");
        }
      printf("\n"); // End of the dump line (each line is 16 bytes)
    } // End if
  } // End for
}

