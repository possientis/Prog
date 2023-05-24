#!/bin/sh

set -e 
DIR=${HOME}/Prog/maven/simple-weather/
cd ${DIR}

mvn install
# cannot run program, yahoo ervice needs authentication
mvn clean
rm velocity.log

echo '\ntest completed successfully\n'
