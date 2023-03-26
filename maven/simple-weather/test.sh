#!/bin/sh

set -e 
DIR=/home/john/Prog/maven/simple-weather/
cd ${DIR}

mvn install
# cannot run program, yahoo ervice needs authentication
mvn clean
rm velocity.log

echo '\ntest completed successfully\n'
