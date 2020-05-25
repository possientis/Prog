#!/bin/sh

DIR=/home/john/Prog/haskell/Set

set -e 
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
