#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c
cd ${HOME}

rm -f a.out
rm -f *.o
rm -f log

./attribute/clean.sh
./bitcoin/clean.sh
./cpp/clean.sh
./cs/clean.sh
./dlopen/clean.sh
./hacking/clean.sh
./gcov/clean.sh
./library/clean.sh
./pragma/clean.sh
./tlpi/clean.sh

cd ${DIR}
