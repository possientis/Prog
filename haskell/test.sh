#!/bin/sh
# need to install ghc

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

ghc -v0 -o a.out hello.hs; ./a.out ; ./clean.sh

./logic/test.sh

cd ${DIR}
echo '\nAll haskell tests completed successfully\n'




