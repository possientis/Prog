#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/maven/simple-weather/
cd ${HOME}

mvn install
# cannot run program, yahoo ervice needs authentication
mvn clean
rm velocity.log


cd ${DIR}
echo '\ntest completed successfully\n'




