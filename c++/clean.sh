#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c++
cd ${HOME}

rm -f *.o
rm -f a.out
./bitcoin/clean.sh

cd ${DIR}
