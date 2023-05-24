#!/bin/sh

set -e 
DIR=${HOME}/Prog/java/bitcoin
cd ${DIR}

rm -f *.class
./compile.sh Test_Main.java 
./run.sh Test_Main
rm -f *.class

echo '\nbitcoinj test completed successfully\n'
