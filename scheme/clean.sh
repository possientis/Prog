#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/scheme
cd ${HOME}

rm -f a.out
rm -f *.o
./guile/clean.sh

cd ${DIR}