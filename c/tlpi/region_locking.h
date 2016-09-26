#ifndef REGION_LOCKIMG_H
#define REGION_LOCKING_H

/* Lock a file region using nonblocking F_SETLK */
int lockRegion(int fd, int type, int whence, int start, int len);


/* Lock a file region using blocking F_SETLKW */
int lockRegionWait(int fd, int type, int whence, int start, int len);


/* Test if a file region is lockable. Return 0 if lockable, or
 * PID of process holding incompatible lock, or -1 on error. */
pid_t regionIsLocked(int fd, int type, int whence, int start, int len);


#endif
