#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/lisp
cd ${HOME}
echo

echo "testing scheme interpreter"

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


cd ${DIR}
echo '\ntest completed successfully\n'




