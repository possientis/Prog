#!/bin/sh

DIR=${HOME}/Prog/c/bitcoin/secp256k1
cd ${DIR}

rm -f *.o
rm -f a.out
./test/clean.sh
