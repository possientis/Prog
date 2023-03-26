#!/bin/sh

DIR=/home/john/Prog/haskell/logic2
cd ${DIR}

rm -f *.hi
rm -f *.o
rm -f a.out

./fopl/clean.sh
./lambda/clean.sh
