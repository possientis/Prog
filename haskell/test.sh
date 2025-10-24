#!/bin/bash
# need to install ghc

set -e 
DIR=${HOME}/Prog/haskell
cd ${DIR}

make -j$(( $(nproc --all) - 1))
cat *.tmp
./clean.sh

echo -e "All haskell tests completed successfully\n"
