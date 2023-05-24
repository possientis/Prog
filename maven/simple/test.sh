#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/simple/
cd ${DIR}

mvn install
java -cp target/simple-1.0-SNAPSHOT.jar org.sonatype.mavenbook.App
mvn clean

echo '\ntest completed successfully\n'
