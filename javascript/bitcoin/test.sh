#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/javascript/bitcoin
cd ${HOME}

BITCOINJ_JARS=

for d in *.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done

jjs -cp "$BITCOINJ_JARS" demo.js

cd ${DIR}
echo '\njjs test completed succesfully\n'



