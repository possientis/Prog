#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/c++/bitcoin
cd ${HOME}

./compile.sh priv.cpp
./a.out
rm a.out

cd ${DIR}
echo '\nlibbitcoin test completed succesfully\n'

