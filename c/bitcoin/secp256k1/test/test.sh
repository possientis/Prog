#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/test
cd ${HOME}

echo
echo "testing main secp256k1 library..."
bash run.sh main 
echo

echo
echo "testing cloned secp256k1 library..."
#bash run.sh clone  # this is broken
echo

cd ${DIR}
echo
echo "All secp256k1 tests completed successfully"
echo




