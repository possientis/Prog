#!/bin/sh

DIR=${HOME}/Prog/c
cd ${DIR}

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

