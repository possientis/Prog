#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/json
cd ${DIR}
echo

echo "testing json parsing..."

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh

echo '\ntest completed successfully\n'
