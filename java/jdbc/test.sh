#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/jdbc
cd ${HOME}

javac JDBCExample1.java;
java -cp /usr/share/java/postgresql.jar:. JDBCExample1
rm *.class


cd ${DIR}
echo '\njdbc test completed succesfully\n'




