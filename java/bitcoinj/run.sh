#!/bin/sh
BITCOINJ_JARS=

BITCOINJ_DIR=`dirname $0`

for d in $BITCOINJ_DIR/*.jar
do
  BITCOINJ_JARS="$d:$BITCOINJ_JARS"
done


java -cp "$BITCOINJ_JARS" "$@"




# bitcoinj-core-0.14.1.jar
# core-1.54.0.0.jar
# guava-19.0.jar
# jcip.jar
# pg-1.54.0.0.jar
# pkix-1.54.0.0.jar
# prov-1.54.0.0.jar
# slf4j-api.jar
# slf4j-jdk14.jar
