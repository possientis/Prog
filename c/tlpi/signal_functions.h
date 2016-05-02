#ifndef SIGNAL_FUNCTIONS_H
#define SIGNAL_FUNCTIONS_H

#include <stdio.h>  // FILE

/* Print list of signals within a signal set */
void printSigset(FILE *of, const char *prefix, const sigset_t *sigset);

/* Print mask of blocked signals for this process */
int printSigMask(FILE *of, const char *msg);

/* Print signals currently pending for this process */
int printPendingSigs(FILE *of, const char *msg);

#endif
