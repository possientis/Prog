#include <stdio.h>
#include <linux/if_ether.h>

struct header1 {
  unsigned char dest[6];
  unsigned char source[6];
  unsigned short  id;
};

struct header2 {
  unsigned char dest[6];
  unsigned char source[6];
  unsigned short  id;
} __attribute__((packed));

int main()
{
  printf("size of 'struct ethhdr' = %d\n", sizeof(struct ethhdr));
  printf("size of 'struct header1 (unpacked)' = %d\n", sizeof(struct header1));
  printf("size of 'struct header2 (packed)' = %d\n", sizeof(struct header2));

  return 0;
}
