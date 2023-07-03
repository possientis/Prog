#!/bin/sh
# need to install ghc

set -e 
DIR=${HOME}/Prog/haskell
cd ${DIR}

make -j$(nproc --all)

cat song.tmp
cat json.tmp
cat Logic.tmp
cat logic2.tmp
cat types.tmp
cat lisp.tmp
cat Optics.tmp
cat adi.tmp
cat adh.tmp
cat Set.tmp

./clean.sh

echo '\nAll haskell tests completed successfully\n'
