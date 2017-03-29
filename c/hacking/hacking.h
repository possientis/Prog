#ifndef INCLUDE_HACKING_H
#define INCLUDE_HACKING_H

#include <string.h>
#include <malloc.h>
#include <stdlib.h>

void fatal(const char *message);
void *ec_malloc(unsigned int size);
void dump(const unsigned char *data_buffer, unsigned int length);

#endif
