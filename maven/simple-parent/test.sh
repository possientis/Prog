#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/maven/simple-parent/
cd ${HOME}

mvn install
mvn clean
rm simple-weather/velocity.log


cd ${DIR}
echo '\ntest completed succesfully\n'




