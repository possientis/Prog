#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c
cd ${HOME}

rm -f a.out
rm -f *.o
rm -f log

./bitcoin/clean.sh
./tlpi/clean.sh
./pragma/clean.sh
./dlopen/clean.sh
./library/clean.sh
./hacking/clean.sh

cd ${DIR}
