#!/bin/sh

set -e
DIR=/home/john/Prog/poly/Bitcoin/Number/scheme
cd ${DIR}

echo '\nThis is Scheme ...'

START=$(date +%s%N)
scm bench-number.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
