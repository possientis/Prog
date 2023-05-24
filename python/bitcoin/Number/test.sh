#!/bin/sh

set -e
DIR=${HOME}/Prog/poly/Bitcoin/Number/python
cd ${DIR}


echo '\nThis is Python ...'

START=$(date +%s%N)
python3 Test_Number.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
