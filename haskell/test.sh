#!/bin/sh
# need to install ghc

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

./json/test.sh
./logic/test.sh
./types/test.sh

cd ${DIR}
echo '\nAll haskell tests completed successfully\n'




