#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/logic/fopl
cd ${HOME}
echo

echo "testing universal algebra of predicate logic"

ghc -o a.out Unit-Test.hs; ./a.out;./clean.sh


cd ${DIR}
echo '\ntest completed successfully\n'




