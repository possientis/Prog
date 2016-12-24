#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number/java
cd ${HOME}

echo '\nThis is Java ...'
./compile.sh Test_Number.java
START=$(date +%s%N)
java Test_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh

cd ${DIR}


