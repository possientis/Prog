#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/json
cd ${HOME}
echo

echo "testing json parsing..."

ghc -o a.out Unit-Test.hs; ./a.out; ./clean.sh


cd ${DIR}
echo '\ntest completed successfully\n'




