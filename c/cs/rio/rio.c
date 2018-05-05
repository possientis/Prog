#include <unistd.h> 
#include <errno.h>

#include "rio.h"


ssize_t rio_readn(int fd, void *usrbuf, size_t n)
{
    size_t nleft = n;
    ssize_t nread;
    char *bufp = (char*) usrbuf;

    while (nleft > 0) {

        if ((nread = read(fd, bufp, nleft)) < 0) {
            if(errno == EINTR)  /* interrupted by sig handler return */
                nread = 0;      /* and call read again */
            else
                return -1;      /* errno set by read() */
        }
        else if (nread == 0)
            break;              /* EOF */

        nleft -= nread;
        bufp  += nread;
    }

    return n - nleft;           /* return >= 0 */

}


ssize_t rio_writen(int fd, const void *usrbuf, size_t n)
{
    size_t nleft = n;
    ssize_t nwritten;
    const char* bufp = usrbuf;

    while (nleft > 0) {

        if((nwritten = write(fd, bufp, nleft)) <= 0) {
            if(errno == EINTR)  /* interrupted by sig handler return */
                nwritten = 0;   /* and call write again */
            else
                return -1;
        }

        nleft -= nwritten;
        bufp  += nwritten;
    }

    return n;
}

