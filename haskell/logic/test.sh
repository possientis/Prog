#!/bin/sh

LOC=/home/john/Prog/haskell/logic/

set -e 
cd ${LOC}

echo
echo "testing logic Haskell formalization..."
echo

ghc -O2 Main.hs
./Main
./clean.sh

echo
echo 'test completed successfully'
echo
