#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f test
rm -f a.out

./bitcoin/clean.sh
./logic/clean.sh
./json/clean.sh
./types/clean.sh


cd ${DIR}
