#!/bin/sh

set -e 
DIR=${HOME}/Prog/java/jdbc
cd ${DIR}

echo '\nJDBCExample1:'
javac JDBCExample1.java;
java -cp /usr/share/java/postgresql.jar:. JDBCExample1 ${USER}

echo '\nJDBCExample2:'
javac JDBCExample2.java
java -cp /usr/share/java/postgresql.jar:. JDBCExample2 ${USER}

rm *.class

echo '\njdbc test completed successfully\n'
