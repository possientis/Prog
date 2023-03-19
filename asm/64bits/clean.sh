#!/bin/sh

DIR=/home/john/Prog/asm/64bits
cd ${DIR}

rm -f *.lst
rm -f *.o
rm -f a.out
rm -f array
rm -f customer.dat
rm -f test

./carry/clean.sh
./cpu/clean.sh
./extern/clean.sh
./hello/clean.sh
./isa/clean.sh
./mul/clean.sh
