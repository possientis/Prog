#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1
cd ${HOME}

rm -f *.o
rm -f a.out
./clone/clean.sh
./test/clean.sh

cd ${DIR}
