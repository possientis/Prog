#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/maven/
cd ${DIR}

gradle init #sets up gradle build from maven?
gradle build
java -cp build/libs/simple-1.0-SNAPSHOT.jar org.sonatype.mavenbook.App
./clean.sh

echo '\ntest completed successfully\n'
