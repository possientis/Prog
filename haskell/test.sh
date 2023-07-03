#!/bin/sh
# need to install ghc

set -e 
DIR=${HOME}/Prog/haskell
cd ${DIR}

make -j$(nproc --all)
cat *.tmp
./clean.sh

echo '\nAll haskell tests completed successfully\n'
