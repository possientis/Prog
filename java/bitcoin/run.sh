#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=`dirname $0`

for d in $BITCOINJ_DIR/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done

# we need java to pick up libsecp256k1.so on current directory
env LD_LIBRARY_PATH=. java -cp "$BITCOINJ_JARS" "$@"


