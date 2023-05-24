#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/parent/
cd ${DIR}

mvn install
mvn clean

echo '\ntest completed successfully\n'
