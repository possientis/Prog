#!/bin/sh

DIR=${HOME}/Prog/haskell/Crypto
cd ${DIR}

rm -f *.hi
rm -f *.o
rm -f test
rm -f a.out

./Number/clean.sh
