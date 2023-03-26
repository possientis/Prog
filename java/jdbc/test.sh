#!/bin/sh

set -e 
DIR=/home/john/Prog/java/jdbc
cd ${DIR}

echo '\nJDBCExample1:'
javac JDBCExample1.java;
java -cp /usr/share/java/postgresql.jar:. JDBCExample1

echo '\nJDBCExample2:'
javac JDBCExample2.java
java -cp /usr/share/java/postgresql.jar:. JDBCExample2

rm *.class

echo '\njdbc test completed successfully\n'
