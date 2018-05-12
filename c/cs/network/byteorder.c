#include <arpa/inet.h>
#include <stdio.h>


int main() 
{

    
    uint32_t l = 0xaabbccdd;
    uint16_t s = 0xaabb;

    printf("l = 0x%x\n", l);
    printf("s = 0x%x\n", s);

    /* 0xddccbbaa on little endian machine. Why is that ?
     * The function htonl assumes its argument is given
     * in 'host' byte order and returns it in 'network'
     * byte order (big endian). 
     *
     * On a big endian machine, it acts asthe identity on uint32_t
     * On a little endian machine, it reverses the byte ordering.
     *
     * Equally ntohl reverses the byte ordering
     */

    printf("htonl(l) = 0x%x\n", htonl(l)); /* 0xddccbbaa */
    printf("ntohl(l) = 0x%x\n", ntohl(l)); /* 0xddccbbaa */
    printf("htons(s) = 0x%x\n", htons(s)); /* 0xbbaa */
    printf("ntohs(s) = 0x%x\n", ntohs(s)); /* 0xbbaa */

    

    return 0;
}
