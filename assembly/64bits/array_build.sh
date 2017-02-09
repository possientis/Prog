#!/bin/sh

./yasm.sh array_main
./yasm.sh array_create
./yasm.sh array_fill
./yasm.sh array_print
./yasm.sh array_min

gcc -static -o array \
  array_main.o \
  array_create.o \
  array_fill.o \
  array_print.o \
  array_min.o
