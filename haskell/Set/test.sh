#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/Set
cd ${DIR}

echo
echo "testing Set Theory ..."
echo

ghc -O2 Main.hs
./Main
./clean.sh

echo
echo 'test completed successfully'
echo
