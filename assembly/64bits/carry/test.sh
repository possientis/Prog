#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/carry
cd ${HOME}
echo

echo "testing carry for 8 bits add"
../yasm.sh add_carry_8bits.asm
gcc test_add_carry_8bits.c add_carry_8bits.o
./a.out; ./clean.sh 

echo "testing carry for 8 bits sub"
../yasm.sh sub_carry_8bits.asm
gcc test_sub_carry_8bits.c sub_carry_8bits.o
./a.out; ./clean.sh 


cd ${DIR}
echo
echo "carry tests completed successfully"
echo




