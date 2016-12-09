#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/wrapper
cd ${HOME}

gradle wrapper
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




