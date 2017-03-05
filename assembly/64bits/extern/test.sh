#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/extern
cd ${HOME}
option=$(sh ../option.sh)

# quad
g++ -c quadFunction.cpp
../yasm.sh quadASMFunction.asm;
g++ $option quad.cpp quadASMFunction.o quadFunction.o; ./a.out; ./clean.sh

gcc -c quadFunction.c
../yasm.sh quadASMFunction.asm;
gcc $option quad.c quadASMFunction.o quadFunction.o; ./a.out; ./clean.sh

# dword
g++ -c dwordFunction.cpp
../yasm.sh dwordASMFunction.asm;
g++ $option dword.cpp dwordASMFunction.o dwordFunction.o; ./a.out; ./clean.sh

gcc -c dwordFunction.c
../yasm.sh dwordASMFunction.asm;
gcc $option dword.c dwordASMFunction.o dwordFunction.o; ./a.out; ./clean.sh

# word
g++ -c wordFunction.cpp
../yasm.sh wordASMFunction.asm;
g++ $option word.cpp wordASMFunction.o wordFunction.o; ./a.out; ./clean.sh

gcc -c wordFunction.c
../yasm.sh wordASMFunction.asm;
gcc $option word.c wordASMFunction.o wordFunction.o; ./a.out; ./clean.sh

# byte
g++ -c byteFunction.cpp
../yasm.sh byteASMFunction.asm;
g++ $option byte.cpp byteASMFunction.o byteFunction.o; ./a.out; ./clean.sh

gcc -c byteFunction.c
../yasm.sh byteASMFunction.asm;
gcc $option byte.c byteASMFunction.o byteFunction.o; ./a.out; ./clean.sh

cd ${DIR}
echo
echo "test completed successfully"
echo




