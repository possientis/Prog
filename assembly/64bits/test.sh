#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

# Hello world!
./as.sh hello_32bits; ld hello_32bits.o; ./a.out; ./clean.sh     # 32 bits at&t
./as.sh hello_syscall; ld hello_syscall.o; ./a.out; ./clean.sh   # 64 bits syscall
./as.sh hello_printf; gcc -static hello_printf.o; ./a.out; ./clean.sh   # c lib
# TODO : hello_write.s

./yasm.sh hello_32bits; ld hello_32bits.o; ./a.out; ./clean.sh   # 32 bits int 
./yasm.sh hello_syscall; ld hello_syscall.o; ./a.out; ./clean.sh # 64 bits syscall
./yasm.sh hello_printf; gcc -static hello_printf.o; ./a.out; ./clean.sh  # c lib
./yasm.sh hello_write; gcc -static hello_write.o; ./a.out; ./clean.sh    # c lib

# intel syntax
./yasm.sh exit; ld exit.o; ./a.out; ./clean.sh             #_start
./yasm.sh memory; gcc memory.o; ./a.out; ./clean.sh        # main , no c lib
./yasm.sh register; ld register.o; ./a.out; ./clean.sh
./array_build.sh; ./array 20; ./clean.sh


# at&t syntax
./as.sh  register; ld register.o; ./a.out; ./clean.sh


cd ${DIR}
echo '\n64 bits tests completed successfully\n'




