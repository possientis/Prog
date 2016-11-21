#ifndef PTY_FORK_H
#define PTY_FORK_H

#include <stdlib.h>
#include <termios.h>
#include <sys/ioctl.h>

pid_t ptyFork(int *masterFd, char *slaveName, size_t snLen,
    const struct termios *slaveTermios, const struct winsize *slaveWS);

#endif
