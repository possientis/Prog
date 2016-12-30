#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

./compile.sh exit; ld exit.o; ./a.out; ./clean.sh
./compile.sh memory; gcc memory.o; ./a.out; ./clean.sh


cd ${DIR}
echo '\n64 bits tests completed successfully\n'




