#!/bin/sh

set -e
DIR=/home/john/Prog/poly/Bitcoin/Number/haskell
cd ${DIR}

echo '\nThis is Haskell ...'
./compile.sh Bench_Number.hs
START=$(date +%s%N)
./Bench_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
