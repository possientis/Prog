#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/
cd ${HOME}

./Number/clean.sh
./secp256k1/clean.sh

rm -f *.o
rm -f a.out

cd ${DIR}
