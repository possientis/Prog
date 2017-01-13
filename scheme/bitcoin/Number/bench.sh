#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number/scheme
cd ${HOME}


echo '\nThis is Scheme ...'

START=$(date +%s%N)
scm bench-number.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh


cd ${DIR}


