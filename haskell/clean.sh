#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f test
rm -f hello
rm -f a.out

./bitcoin/clean.sh


cd ${DIR}
