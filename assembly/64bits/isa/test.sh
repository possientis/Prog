#!/bin/bash

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits/isa
cd ${HOME}
echo
echo "testing X86_64 isa..."

T1=(adc add and cmp mov or sbb sub xor)

for i in ${T1[@]}
do
  echo "testing $i..."
  bash source.sh $i; yasm -f elf64 $i.asm; ld $i.o; ./a.out
done

./clean.sh


cd ${DIR}
echo
echo "test completed successfully"
echo



