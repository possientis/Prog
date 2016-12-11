#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/dependency/
cd ${HOME}

gradle third

cd ${DIR}
echo '\ntest completed successfully\n'




