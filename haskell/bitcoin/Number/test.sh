#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number/haskell
cd ${HOME}


echo '\nThis is Haskell ...'
./compile.sh Test_Number.hs
START=$(date +%s%N)
./Test_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh


cd ${DIR}


