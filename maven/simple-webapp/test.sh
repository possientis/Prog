#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/maven/simple-webapp/
cd ${HOME}

mvn install
# not sure how to test program
mvn clean


cd ${DIR}
echo '\ntest completed successfully\n'




