#ifndef ITIMERSPEC_FROM_STR_H
#define ITIMERSPEC_FROM_STR_H
struct itimerspec;
struct timespec;

void itimerspecFromStr(char *str, struct itimerspec *tsp);

#endif
