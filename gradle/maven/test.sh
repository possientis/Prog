#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/maven/
cd ${HOME}

gradle init #sets up gradle build from maven?
gradle build
java -cp build/libs/simple-1.0-SNAPSHOT.jar org.sonatype.mavenbook.App
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




