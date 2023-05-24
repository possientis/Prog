#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/simple-parent/
cd ${DIR}

mvn install
mvn clean
rm simple-weather/velocity.log

echo '\ntest completed successfully\n'
