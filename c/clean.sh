#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c
cd ${HOME}

rm -f a.out
rm -f *.o
./bitcoin/clean.sh
./tlpi/clean.sh

cd ${DIR}