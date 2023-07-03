#!/bin/sh

DIR=${HOME}/Prog/haskell
cd ${DIR}

rm -f *.hi
rm -f *.o
rm -f test
rm -f a.out

rm -f song.tmp
rm -f json.tmp
rm -f Logic.tmp
rm -f logic2.tmp
rm -f types.tmp
rm -f lisp.tmp
rm -f Optics.tmp
rm -f adi.tmp
rm -f adh.tmp
rm -f Set.tmp



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
