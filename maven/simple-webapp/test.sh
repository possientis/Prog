#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/simple-webapp/
cd ${DIR}

mvn install
# not sure how to test program
mvn clean

echo '\ntest completed successfully\n'
