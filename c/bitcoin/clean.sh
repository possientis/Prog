#!/bin/sh

DIR=/home/john/Prog/c/bitcoin/
cd ${DIR}

./Number/clean.sh
./secp256k1/clean.sh

rm -f *.o
rm -f a.out

