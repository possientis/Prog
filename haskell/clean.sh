#!/bin/sh

DIR=/home/john/Prog/haskell
cd ${DIR}

rm -f *.hi
rm -f *.o
rm -f test
rm -f a.out

./song/clean.sh
./bitcoin/clean.sh
./lisp/clean.sh
./Logic/clean.sh
./logic2/clean.sh
./json/clean.sh
./parconc/clean.sh
./types/clean.sh
./wiwik/clean.sh
./Optics/clean.sh
./adi/clean.sh
./adh/clean.sh
./Set/clean.sh
./Crypto/clean.sh
