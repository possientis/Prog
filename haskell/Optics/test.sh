#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/Optics/
cd ${DIR}
echo
echo "testing logic Haskell optics..."

ghc -O2 Main.hs
./Main
./clean.sh

echo '\ntest completed successfully\n'
