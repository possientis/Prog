#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=$(dirname $0)

for d in $BITCOINJ_DIR/lib/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done


jjs -cp "$BITCOINJ_JARS" "$@"


