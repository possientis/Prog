#!/bin/sh
JDBC_JARS=
for d in `dirname $0`/*.jar
do
    JDBC_JARS="$d:$JDBC_JARS"
done

# echo $JDBC_JARS

# compiling while suppressing stdout comment
clojurec -cp "$JDBC_JARS" "$@" 1> /dev/null

# running program
java -cp "$JDBC_JARS" "$@"

# clean up
rm *.class; rm clojure/java/*.class; rm clojure/java/jdbc/*.class
