#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/types
cd ${HOME}
echo

echo "testing types and programming languages..."

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


cd ${DIR}
echo '\ntest completed successfully\n'




