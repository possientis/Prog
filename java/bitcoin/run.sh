#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=`dirname $0`

for d in $BITCOINJ_DIR/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done


java -cp "$BITCOINJ_JARS" "$@"


