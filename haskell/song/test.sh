#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/song
cd ${HOME}
echo
echo "testing jimmy song's bitcoin"

ghc -O2 -o a.out Main.hs; ./a.out; ./clean.sh

cd ${DIR}
echo '\nAll jimmy song tests complete successfully\n'




