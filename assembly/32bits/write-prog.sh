#!/bin/sh
# creates file test.dat

set -e
as --32 -o write-record.o write-record.s
as --32 -o write-prog.o write-prog.s
ld -m elf_i386 -o write-prog write-prog.o write-record.o
./write-prog
rm write-prog write-prog.o write-record.o
