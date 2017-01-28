#!/bin/sh
# need to install ghc

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

ghc -v0 hello.hs
./hello
./clean.sh

cd ${DIR}
echo '\nAll haskell tests completed successfully\n'




