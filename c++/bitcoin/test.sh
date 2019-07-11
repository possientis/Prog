#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/c++/bitcoin
cd ${HOME}

LD_LIBRARY_PATH="/home/john/Libs/secp256k1/.libs"

./compile.sh priv.cpp
export LD_LIBRARY_PATH
./a.out
./clean.sh

cd ${DIR}
echo '\nlibbitcoin test completed successfully\n'

