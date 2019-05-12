#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/logic
cd ${HOME}
echo
echo "testing logic formalization..."

ghc -O2 Main.hs
./Main

echo
echo "Testing coq formalization..."
make
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




