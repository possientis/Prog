#!/bin/sh

set -e 
DIR=${HOME}/Prog/asm/64bits/mul
cd ${DIR}
echo

option=$(sh ../option.sh)

echo "testing 8 bits unsigned multiplication..." 
../yasm.sh test_mul_8bits.asm 
gcc test_mul_8bits.c test_mul_8bits.o
./a.out; ./clean.sh
echo

echo "testing 16 bits unsigned multiplication..." 
../yasm.sh test_mul_16bits.asm 
gcc test_mul_16bits.c test_mul_16bits.o
./a.out; ./clean.sh
echo

echo "testing 32 bits unsigned multiplication..." 
../yasm.sh test_mul_32bits.asm 
gcc test_mul_32bits.c test_mul_32bits.o
./a.out; ./clean.sh
echo

echo "testing 64 bits unsigned multiplication..."
../yasm.sh test_mul_64bits.asm
gcc $option test_mul_64bits.c test_mul_64bits.o
./a.out; ./clean.sh
echo

echo "testing 8 bits signed multiplication..." 
../yasm.sh test_imul_8bits.asm 
gcc test_imul_8bits.c test_imul_8bits.o
./a.out; ./clean.sh
echo

echo "testing 16 bits signed multiplication..." 
../yasm.sh test_imul_16bits.asm 
gcc test_imul_16bits.c test_imul_16bits.o
./a.out; ./clean.sh
echo

echo "testing 32 bits signed multiplication..." 
../yasm.sh test_imul_32bits.asm 
gcc test_imul_32bits.c test_imul_32bits.o
./a.out; ./clean.sh
echo

# TODO 64 bits signed multiplication

echo
echo "multiplication tests completed successfully"
echo




