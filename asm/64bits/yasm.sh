#!/bin/sh

# The -f elf64 option selects a 64 bit output format 
# which is compatible with Linux and gee

# The -g dwarf2 option selects the dwarf2 debugging
# format, which is essential for use with a debugger

# The -1 exit . 1st asks for a listing file which 
# shows the generated code in hexadecimal.

name=$(basename "$1" .asm)

yasm -f elf64 -g dwarf2 -l $name.lst $name.asm 

