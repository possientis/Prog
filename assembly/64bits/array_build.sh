#!/bin/sh

./compile.sh array_main
./compile.sh array_create
./compile.sh array_fill
./compile.sh array_print
./compile.sh array_min

gcc -static -o array \
  array_main.o \
  array_create.o \
  array_fill.o \
  array_print.o \
  array_min.o
