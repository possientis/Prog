#!/bin/sh
RABBIT_JARS=
for d in `dirname $0`/*.jar
do
    RABBIT_JARS="$d:$RABBIT_JARS"
done

clojurec -cp "$RABBIT_JARS" "$@" 1> /dev/null
java -cp "$RABBIT_JARS" "$@"
rm *.class
