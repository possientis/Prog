#!/bin/sh

DIR=${HOME}/Prog/haskell/adh

set -e 
cd ${DIR}

echo
echo "testing Algorithm design in Haskell..."
echo

ghc -O2 -Wall Main.hs
./Main
./clean.sh

echo
echo 'test completed successfully'
echo
