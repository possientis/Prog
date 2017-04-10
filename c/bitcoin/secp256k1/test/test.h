#ifndef INCLUDED_TEST_H
#define INCLUDED_TEST_H

#include <stddef.h>

void default_callback(const char* message, void* data);
int buffer_equals(const void *ptr, const void* qtr, size_t size);
void buffer_clear(void *ptr, size_t size);
int buffer_null(const void *ptr, size_t size);


#endif
