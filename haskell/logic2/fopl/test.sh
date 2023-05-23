#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/logic2/fopl
cd ${DIR}
echo

echo "testing universal algebra of predicate logic"

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


echo '\ntest completed successfully\n'
