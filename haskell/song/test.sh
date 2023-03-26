#!/bin/sh

set -e 
DIR=/home/john/Prog/haskell/song
cd ${DIR}
echo
echo "testing jimmy song's bitcoin"

ghc -O2 -o a.out Main.hs; ./a.out; ./clean.sh

echo '\nAll jimmy song tests complete successfully\n'
