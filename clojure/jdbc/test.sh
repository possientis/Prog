#!/bin/sh

set -e 
DIR=${HOME}/Prog/clojure/jdbc
cd ${DIR}

JDBC_JARS=
for d in *.jar
do
    JDBC_JARS="$d:$JDBC_JARS"
done

# compiling while suppressing stdout comment
clojurec -cp "$JDBC_JARS" test_java_jdbc 1> /dev/null

# running program
java -cp "$JDBC_JARS" test_java_jdbc ${USER}

# clean up
./clean.sh

echo '\njdbc test completed successfully\n'

