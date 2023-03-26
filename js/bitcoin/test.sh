#!/bin/sh

set -e 
DIR=/home/john/Prog/js/bitcoin
cd ${DIR}

BITCOINJ_JARS=

for d in lib/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done

jjs -cp "$BITCOINJ_JARS" test.js

echo '\njjs test completed successfully\n'
