#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=$(dirname $0)

for d in $BITCOINJ_DIR/lib/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done

# we need java to pick up libsecp256k1.so on current directory
# having library on the class path does not make it work, hence
# we need to set the LD_LIBRARY_PATH environment variable 

env LD_LIBRARY_PATH=$BITCOINJ_DIR/lib java -cp "$BITCOINJ_JARS:" "$@"




