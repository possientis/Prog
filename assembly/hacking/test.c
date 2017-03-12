#include <stdio.h>

#include "hacking-network.h"

int main()
{

  printf("ether size = %d\n", sizeof(struct ether_hdr));
  printf("ip size = %d\n", sizeof(struct ip_hdr));
  printf("tcp size = %d\n", sizeof(struct tcp_hdr));

  return 0;
}
