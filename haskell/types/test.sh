#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/types
cd ${DIR}
echo

echo "testing types and programming languages..."

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


echo '\ntest completed successfully\n'
