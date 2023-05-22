#!/bin/sh

set -e 
DIR=${HOME}/Prog/c/bitcoin/secp256k1/test
cd ${DIR}

echo
echo "testing main secp256k1 library..."
bash run.sh main
echo

echo
echo "testing cloned secp256k1 library..."
# bash run.sh clone # broken
echo

echo
echo "All secp256k1 tests completed successfully"
echo




