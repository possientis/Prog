#!/bin/sh

DIR=${HOME}/Prog/make
cd ${DIR}

./guile/clean.sh
./jupiter/clean.sh
./mars/clean.sh
./saturn/clean.sh
./test/clean.sh

rm -f *.tmp
