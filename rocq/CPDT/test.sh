#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/CPDT
cd ${DIR}
echo
echo "testing CPDT..."

ghc Main.hs
./Main
make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
