/* for some reason, the programmer should define this himself */
/* rather than it being part of system files */
#ifndef SEMUN_H
#define SEMUN_H

#include <sys/types.h> /* For portability */
#include <sys/sem.h>  

union semun {
  int       val;
  struct semid_ds *buf;
  unsigned short *array;
#if defined(__linux__)
    struct seminfo *_buf;
#endif
};

#endif
