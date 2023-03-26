#!/bin/sh

set -e 
DIR=/home/john/Prog/maven/parent/
cd ${DIR}

mvn install
mvn clean

echo '\ntest completed successfully\n'
