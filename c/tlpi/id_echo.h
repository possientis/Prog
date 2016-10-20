/* Header file for id_echo_sv.c and id_echo_cl.c */

#ifndef ID_ECHO_H
#define ID_ECHO_H

#include "inet_sockets.h"
#include "tlpi_hdr.h"       /* Declares our socket functions */

#define SERVICE "echo"      /* Name of UDP service */

#define BUF_SIZE 500        /* Maximum size of datagrams that can
                             * be read by client and server */

#endif
