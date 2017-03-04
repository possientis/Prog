#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/extern
cd ${HOME}
option=$(sh ../option.sh)

# quad
g++ -c functions.cpp
../yasm.sh ASMFunctions2.asm;
g++ $option quad.cpp ASMFunctions2.o functions.o; ./a.out; ./clean.sh

../yasm.sh ASMFunctions.asm;
gcc $option quad.c ASMFunctions.o; ./a.out; ./clean.sh

# dword
../yasm.sh ASMFunctions.asm;
g++ $option dword.cpp ASMFunctions.o; ./a.out; ./clean.sh

../yasm.sh ASMFunctions.asm;
gcc $option dword.c ASMFunctions.o; ./a.out; ./clean.sh

# word
../yasm.sh ASMFunctions.asm;
g++ $option word.cpp ASMFunctions.o; ./a.out; ./clean.sh

../yasm.sh ASMFunctions.asm;
gcc $option word.c ASMFunctions.o; ./a.out; ./clean.sh

# byte
../yasm.sh ASMFunctions.asm;
g++ $option byte.cpp ASMFunctions.o; ./a.out; ./clean.sh

../yasm.sh ASMFunctions.asm;
gcc $option byte.c ASMFunctions.o; ./a.out; ./clean.sh

cd ${DIR}
echo
echo "test completed successfully"
echo




