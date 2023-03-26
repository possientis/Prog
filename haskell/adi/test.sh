#!/bin/sh

set -e 
DIR=/home/john/Prog/haskell/adi
cd ${DIR}

echo
echo "testing Abstracting Definitional Interpreter..."
echo

ghc -O2 -Wall Main.hs
./Main
./clean.sh

echo
echo 'test completed successfully'
echo
