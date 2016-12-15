#!/bin/sh

# you may need to install packages gcc-multilib and g++-multilib

set -e

# dynamic linking -> executable really finalized at program 
# start-up time after library is loaded by dynamic linker 
# and addresses of 'printf' and 'exit' are known.
as --32 -o helloworld-lib.o helloworld-lib.s
# linking can be done with the usual 'ld' or with 'gcc'
# however, gcc linking seems to require the entry point to be 'main'
# rather than '_start'. As can be seen, gcc linking is a lot easier
#
# ld syntax is explained as follows:
# -m elf_i386 -> creating 32 bit elf executable
# -e main     -> entry point called 'main' rather than '_start' 
# -dynamic-linker /lib/ld-linux.so.2  -> library (printf, exit see below)
# -lc         -> also necessary in order to link to C library (see below)
# -o helloworld-lib -> name of output executable file
#
# reference:
# https://stackoverflow.com/questions/34374591/linking-an-assembler-program-error-undefined-reference-to-printf

#
ld -melf_i386 -e main -dynamic-linker /lib/ld-linux.so.2 -o helloworld-lib helloworld-lib.o -lc
#gcc -m32 helloworld-lib.o -o helloworld-lib
#./helloworld-lib
#rm helloworld-lib helloworld-lib.o
#
#The option -dynamic-linker /lib/ld-linux.so.2 allows our program to be linked to
#libraries. This builds the executable so that before executing, the operating system will load the
#program /lib/ld-linux.so.2 to load in external libraries and link them with the program.
#This program is known as a dynamic linker.
#The -lc option says to link to the c library, named libc.so on GNU/Linux systems. Given a
#library name, c in this case (usually library names are longer than a single letter), the GNU/Linux
#linker prepends the string lib to the beginning of the library name and appends .so to the end of
#it to form the library’s filename. This library contains many functions to automate all types of
#tasks. The two we are using are printf , which prints strings, and exit , which exits the program.
./helloworld-lib
rm helloworld-lib helloworld-lib.o
