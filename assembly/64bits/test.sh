#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

# intel syntax
./yasm.sh exit; ld exit.o; ./a.out; ./clean.sh             #_start
./yasm.sh memory; gcc memory.o; ./a.out; ./clean.sh        # main , no c lib
./yasm.sh hello1; gcc -static hello1.o; ./a.out; ./clean.sh  # main, c lib
./yasm.sh hello2; ld hello2.o; ./a.out; ./clean.sh           # syscall
./yasm.sh register; ld register.o; ./a.out; ./clean.sh
./array_build.sh; ./array 20; ./clean.sh


# at&t syntax
./as.sh  register; ld register.o; ./a.out; ./clean.sh


cd ${DIR}
echo '\n64 bits tests completed successfully\n'




