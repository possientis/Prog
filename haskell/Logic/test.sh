#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/Logic/
cd ${DIR}

echo
echo "testing logic Haskell formalization..."
echo

ghc -O2 Main.hs
./Main
./clean.sh

echo
echo 'test completed successfully'
echo
