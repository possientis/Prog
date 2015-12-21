#!/bin/sh

as --32 -o hello.o hello.s        # --32 to produce 32 bits code
ld -m elf_i386 -o hello hello.o   # -m elf_i386 to link to 32 bit lib
./hello
rm hello.o
rm hello

