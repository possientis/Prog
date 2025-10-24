#!/bin/sh
# need to install ghc

set -e 
DIR=${HOME}/Prog/haskell
cd ${DIR}

make -j$(( $(nproc --all) - 1))
cat *.tmp
./clean.sh

echo '\nAll haskell tests completed successfully\n'
