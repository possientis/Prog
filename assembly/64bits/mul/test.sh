#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/mul
cd ${HOME}
echo

echo "testing 8 bits unsigned multiplication ..." 
../yasm.sh test_mul_8bits.asm 
gcc test_mul_8bits.c test_mul_8bits.o
./a.out; ./clean.sh
echo

echo "testing 16 bits unsigned multiplication ..." 
../yasm.sh test_mul_16bits.asm 
gcc test_mul_16bits.c test_mul_16bits.o
./a.out; ./clean.sh
echo

echo "testing 32 bits unsigned multiplication ..." 
../yasm.sh test_mul_32bits.asm 
gcc test_mul_32bits.c test_mul_32bits.o
./a.out; ./clean.sh
echo



cd ${DIR}
echo
echo "multiplication tests completed successfully"
echo



