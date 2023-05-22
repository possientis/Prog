#!/bin/sh

set -e
DIR=${HOME}/Prog/c++/bitcoin
cd ${DIR}

LD_LIBRARY_PATH="${HOME}/Libs/secp256k1/.libs"

./compile.sh priv.cpp
export LD_LIBRARY_PATH
./a.out
./clean.sh

echo '\nlibbitcoin test completed successfully\n'

