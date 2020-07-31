#!/bin/sh

DIR=/home/john/Prog/haskell/Logic/

set -e 
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
