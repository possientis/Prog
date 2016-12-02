#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/bitcoin
cd ${HOME}

rm -f *.class
./compile.sh Test_Main.java 
./run.sh Test_Main
rm -f *.class

cd ${DIR}
echo '\nbitcoinj test completed succesfully\n'
