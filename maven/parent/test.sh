#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/parent/
cd ${DIR}

mvn install
mvn clean
rm -rf simple-webapp/target

echo '\ntest completed successfully\n'
