#!/bin/sh

set -e
DIR=${HOME}/Prog/poly/Bitcoin/Number/java
cd ${DIR}

echo '\nThis is Java ...'
./compile.sh Bench_Number.java
START=$(date +%s%N)
java Bench_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
