#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell
cd ${HOME}

ghc -v0 hello.hs
./hello
rm hello hello.o hello.hi

cd ${DIR}
echo '\nAll haskell tests completed succesfully\n'




