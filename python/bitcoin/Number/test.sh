#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number/python
cd ${HOME}


echo '\nThis is Python ...'

START=$(date +%s%N)
python3 Test_Number.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh


cd ${DIR}


