#!/bin/sh
# read first names from file test.dat
# run write-prog.sh to create that file first

as --32 -o read-prog-alloc.o read-prog-alloc.s
as --32 -o read-record.o read-record.s
as --32 -o count-chars.o count-chars.s
as --32 -o write-newline.o  write-newline.s
as --32 -o alloc.o alloc.s
ld -m elf_i386 -o read-prog-alloc \
  read-prog-alloc.o read-record.o count-chars.o write-newline.o alloc.o
./read-prog-alloc

rm read-prog-alloc read-prog-alloc.o read-record.o count-chars.o write-newline.o alloc.o


