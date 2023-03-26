#!/bin/sh
# libghc-monadcryptorandom-dev
# libghc-hashable-dev

set -e
DIR=/home/john/Prog/poly/Bitcoin/Number/haskell
cd ${DIR}


echo '\nThis is Haskell ...'
./compile.sh Test_Number.hs
START=$(date +%s%N)
./Test_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
