#!/bin/sh

set -e
DIR=/home/john/Prog/c++/bitcoin
cd ${DIR}

LD_LIBRARY_PATH="/home/john/Libs/secp256k1/.libs"

./compile.sh priv.cpp
export LD_LIBRARY_PATH
./a.out
./clean.sh

echo '\nlibbitcoin test completed successfully\n'

