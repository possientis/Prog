#ifndef RIO_INCLUDE_H
#define RIO_INCLUDE_H

#include <stdlib.h>  /* ssize_t, size_t */

#define RIO_BUFSIZE 8192

typedef struct {
    int rio_fd;                 /* descriptor for this internal buffer */
    int rio_cnt;                /* unread bytes in internal buffer */
    char *rio_bufptr;           /* next unread byte in internal bufer */
    char rio_buf[RIO_BUFSIZE];  /* internal buffer */
} rio_t; 

/* returns number of bytes transferred, 0 on EOF, -1 on error */
ssize_t rio_readn(int fd, void *usrbuf, size_t n);

/* return number of bytes transferred, -1 on error */
ssize_t rio_writen(int fd, const void *usrbuf, size_t n);

void rio_readinitb(rio_t *rp, int fd);

ssize_t rio_readlineb(rio_t *rp, void *usrbuf, size_t maxlen);

/* returns number of bytes transferred, 0 on EOF, -1 on error */
ssize_t rio_readnb(rio_t *rp, void *usrbuf, size_t n);

#endif
