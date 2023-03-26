#!/bin/sh

set -e 
DIR=/home/john/Prog/haskell/lisp
cd ${DIR}
echo

echo "testing scheme interpreter"

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


echo '\ntest completed successfully\n'
