#!/bin/sh
# need to install ghc

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

./song/test.sh
./json/test.sh
./Logic/test.sh
./logic2/test.sh
./types/test.sh
./lisp/test.sh
./Optics/test.sh
./adi/test.sh
./Set/test.sh

cd ${DIR}
echo '\nAll haskell tests completed successfully\n'




