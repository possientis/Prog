#include <stdio.h>
#include <arpa/inet.h>

/* from netinet/in.h
   Internet address.  
typedef uint32_t in_addr_t;
struct in_addr
  {
    in_addr_t s_addr;
  };
*/

int main()
{
    struct in_addr inp;
    const char *s = "128.2.194.242";
    int x;

    x = inet_aton(s, &inp);
    if (x == 1) {
        printf("%s was successfully converted to an internet address\n", s);
        printf("address = 0x%x\n", inp.s_addr);
    } else 
        printf("conversion failed\n");


    char *t;

    /* guessing the returned pointer is statically allocated */
    /* function probably not reentrant */
    t = inet_ntoa(inp);

    printf("t = %s\n", t);


    return 0;



}
