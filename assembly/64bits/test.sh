#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

# hello world
./hello/test.sh

# intel syntax
./yasm.sh exit.asm; ld exit.o; ./a.out; ./clean.sh             #_start
./yasm.sh memory.asm; gcc memory.o; ./a.out; ./clean.sh        # main , no c lib
./array_build.sh; ./array 20; ./clean.sh
./yasm.sh register.asm; ld register.o; ./a.out; ./clean.sh


# at&t syntax
./as.sh  register.s; ld register.o; ./a.out; ./clean.sh


cd ${DIR}
echo
echo "64 bits tests completed successfully"
echo




