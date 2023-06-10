#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/logic2/lambda
cd ${DIR}
echo

echo "testing lambda calculus"

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh

echo '\ntest completed successfully\n'
