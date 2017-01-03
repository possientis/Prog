#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/maven/
cd ${HOME}

mvn install
java -cp target/simple-1.0-SNAPSHOT.jar org.sonatype.mavenbook.App
mvn clean


cd ${DIR}
echo '\ntest completed successfully\n'




