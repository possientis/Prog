#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/jdbc
cd ${HOME}

echo '\nJDBCExample1:'
javac JDBCExample1.java;
java -cp /usr/share/java/postgresql.jar:. JDBCExample1

echo '\nJDBCExample2:'
javac JDBCExample2.java
java -cp /usr/share/java/postgresql.jar:. JDBCExample2

rm *.class

cd ${DIR}
echo '\njdbc test completed successfully\n'




