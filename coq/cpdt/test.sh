#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/cpdt
cd ${DIR}
echo
echo "testing cpdt..."

ghc Main.hs
./Main
make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
