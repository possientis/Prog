#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/jdbc
cd ${HOME}

JDBC_JARS=
for d in *.jar
do
    JDBC_JARS="$d:$JDBC_JARS"
done

# compiling while suppressing stdout comment
clojurec -cp "$JDBC_JARS" test_java_jdbc 1> /dev/null

# running program
java -cp "$JDBC_JARS" test_java_jdbc

# clean up
./clean.sh

cd ${DIR}
echo '\njdbc test completed successfully\n'




