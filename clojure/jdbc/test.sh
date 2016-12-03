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
rm *.class 
rm -f clojure/*.class   # TODO investigate diff of behaviour front v back
rm clojure/java/*.class 
rm clojure/java/jdbc/*.class

cd ${DIR}
echo '\njdbc test completed succesfully\n'




