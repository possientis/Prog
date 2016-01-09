#!/bin/sh
# this assumes test.dat file already exists
# run the program write-prog if not

as --32 -o write-record.o write-record.s
as --32 -o read-record.o read-record.s
as --32 -o add-year-with-check.o add-year-with-check.s
as --32 -o error-exit.o error-exit.s
as --32 -o write-newline.o write-newline.s
as --32 -o count-chars.o count-chars.s

ld -m elf_i386 -o add-year-with-check add-year-with-check.o \
   write-record.o read-record.o error-exit.o write-newline.o count-chars.o

./add-year-with-check

#rm add-year-with-check add-year-with-check.o write-record.o read-record.o \
#  error-exit.o write-newline.o count-chars.o
