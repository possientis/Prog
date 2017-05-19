#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/logic/lambda
cd ${HOME}
echo

echo "testing lambda calculus"

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


cd ${DIR}
echo '\ntest completed successfully\n'




