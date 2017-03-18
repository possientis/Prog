#include <stdio.h>

struct card {
  unsigned int suit : 2;        // can hold values from 0 to 3
  unsigned int face_value : 4;  // can hold values from 0 to 15
} __attribute__ ((packed));

struct pcard {
  int suit : 2;                 // can hold values from -2 to 1
  int face_value : 4;           // can hold values from -8 to 7
};


int main()
{
  printf("size of struct card = %d\n", sizeof(struct card));
  printf("size of struct pcard = %d\n", sizeof(struct pcard));

  int i;
  unsigned char byte;
  struct card c;

  for(i = 0; i < 256; ++i) {

    byte = i;

    *((unsigned char*) &c) = byte;

    printf("byte = 0x%02x:\t suit = %d:\t value = %d\n", i, c.suit, c.face_value);

  }

  return 0;
}
