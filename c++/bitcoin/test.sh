#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/c++/bitcoin
cd ${HOME}

./compile.sh priv.cpp
./a.out
./clean.sh

cd ${DIR}
echo '\nlibbitcoin test completed successfully\n'

