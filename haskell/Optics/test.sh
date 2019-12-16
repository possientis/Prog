#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/Optics/
cd ${HOME}
echo
echo "testing logic Haskell optics..."

ghc -O2 Main.hs
./Main
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




