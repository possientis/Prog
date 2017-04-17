#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

rm -f *.lst
rm -f *.o
rm -f a.out
rm -f array
rm -f customer.dat
rm -f test

./hello/clean.sh
./extern/clean.sh
./mul/clean.sh
./carry/clean.sh
./cpu/clean.sh

cd ${DIR}
