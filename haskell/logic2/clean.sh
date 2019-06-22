#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell/logic2
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f a.out

./fopl/clean.sh
./lambda/clean.sh


cd ${DIR}
