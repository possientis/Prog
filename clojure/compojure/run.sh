#!/bin/sh

COMPOJURE_JARS=
for d in `dirname $0`/*.jar
do
    COMPOJURE_JARS="$d:$COMPOJURE_JARS"
done

echo $COMPOJURE_JARS

clojurec -cp "$COMPOJURE_JARS" "$@" 1> /dev/null
# java -cp "$COMPOJURE_JARS" "$@"
rm *.class; rm compojure/*.class
