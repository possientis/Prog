#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/ant
cd ${HOME}

gradle hello

cd ${DIR}
echo '\ntest completed successfully\n'




