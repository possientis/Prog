#!/bin/sh
# need to install ghc

set -e 
DIR=/home/john/Prog/haskell
cd ${DIR}

./song/test.sh
./json/test.sh
./Logic/test.sh
./logic2/test.sh
./types/test.sh
./lisp/test.sh
./Optics/test.sh
./adi/test.sh
./adh/test.sh
./Set/test.sh

echo '\nAll haskell tests completed successfully\n'
