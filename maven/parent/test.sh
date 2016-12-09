#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/maven/parent/
cd ${HOME}

mvn install
mvn clean


cd ${DIR}
echo '\ntest completed successfully\n'




