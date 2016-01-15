#!/bin/sh

as --32 -o printf-example.o printf-example.s

ld -melf_i386 -lc -o printf-example printf-example.o \
  -dynamic-linker /lib/ld-linux.so.2

./printf-example

rm printf-example printf-example.o
