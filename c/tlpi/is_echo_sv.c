/* A concurrent server that implements the TCP echo service */

#include <signal.h>
//#include <syslog.h> (replacing by fprintf, in case syslog fails)
#include <sys/wait.h>
#include "become_daemon.h"
#include "inet_sockets.h"   /* Declarations of inet*() socket functions */
#include "tlpi_hdr.h"

#define SERVICE "echo"      /* Name of TCP service */
#define BUF_SIZE 4096

static void                 /* SIGCHLD handler to reap dead child processes */
grimReaper(int sig)
{
  int savedErrno;           /* Save 'errno' in case changed here */

  savedErrno = errno;

  while (waitpid(-1, NULL, WNOHANG) > 0)
    continue;

  errno = savedErrno;
}

/* Handle a client request: copy socket input back to socket */

static void
handleRequest(int cfd)
{
  char buf[BUF_SIZE];
  ssize_t numRead;

  while ((numRead = read(cfd, buf, BUF_SIZE)) > 0) {
    if (write(cfd, buf, numRead) != numRead) {
      fprintf(stderr, "write() failed: %s", strerror(errno));
      fflush(stderr);
      exit(EXIT_FAILURE);
    }
  }

  if (numRead == -1) {
    fprintf(stderr, "Error from read(): %s", strerror(errno));
    fflush(stderr);
    exit(EXIT_FAILURE);
  }
}

int
main(int argc, char *argv[])
{
  int lfd, cfd;  /* Listening and connected sockets */
  struct sigaction sa;

  if (becomeDaemon(0) == -1)
    errExit("becomeDaemon");

  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART;
  sa.sa_handler = grimReaper;
  if (sigaction(SIGCHLD, &sa, NULL) == -1) {
    fprintf(stderr, "Error from sigaction(): %s", strerror(errno));
    fflush(stderr);
    exit(EXIT_FAILURE);
  }

  lfd = inetListen(SERVICE, 10, NULL);

  if (lfd == -1) {
    fprintf(stderr, "Could not create server socket (%s)", strerror(errno));
    fflush(stderr);
    exit(EXIT_FAILURE);
  }

  for (;;) {
    cfd = accept(lfd, NULL, NULL); /* Wait for connection */
    if (cfd == -1) {
      fprintf(stderr, "Failure in accept(): %s", strerror(errno));
      fflush(stderr);
      exit(EXIT_FAILURE);
    }

    /* Handle each client request in a new child process */

    switch (fork()) {
      case -1:
        fprintf(stderr, "Can't create child (%s)", strerror(errno));
        fflush(stderr);
        close(cfd);         /* Give up on this client */
        break;              /* May be temporary; try next client */
      case 0:               /* Child */
        close(lfd);         /* Unneeded copy of listening socket */
        handleRequest(cfd);
        _exit(EXIT_SUCCESS);

      default:              /* Parent */
        close(cfd);         /* Unneeded copy of connected socket */
        break;              /* Loop to accept next connection */
    }
  }
}
