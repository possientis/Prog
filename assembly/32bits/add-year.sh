#!/bin/sh
# this assumes test.dat file already exists
# run the program write-prog if not

set -e
as --32 -o write-record.o write-record.s
as --32 -o read-record.o read-record.s
as --32 -o add-year.o add-year.s
ld -m elf_i386 -o add-year add-year.o write-record.o read-record.o
./add-year
rm add-year add-year.o write-record.o read-record.o
