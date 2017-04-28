#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/test
cd ${HOME}

rm -f *.o
rm -f a.out
rm -f log{,1,2} # brace expansion requires bash

cd ${DIR}
