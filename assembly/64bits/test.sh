#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

# hello world
./hello/test.sh

# intel syntax
./yasm.sh register.asm; ld register.o; ./a.out; ./clean.sh

# at&t syntax
./as.sh  register.s; ld register.o; ./a.out; ./clean.sh

# c++
./yasm.sh ASMFunctions.asm;
g++ -no-pie extern.cpp ASMFunctions.o; ./a.out; ./clean.sh


cd ${DIR}
echo
echo "64 bits tests completed successfully"
echo




