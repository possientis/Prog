#!/bin/sh

./yasm.sh array_main.asm
./yasm.sh array_create.asm
./yasm.sh array_fill.asm
./yasm.sh array_print.asm
./yasm.sh array_min.asm

gcc $(sh option.sh) -o array \
  array_main.o \
  array_create.o \
  array_fill.o \
  array_print.o \
  array_min.o
