#!/bin/sh

set -e

as --32 -o ${1}.o ${1}.s          # --32 to produce 32 bits code
ld -m elf_i386 -o $1 ${1}.o       # -m elf_i386 to link to 32 bit lib
./$1
rm ${1}.o
rm $1

