#!/bin/sh

set -e 
DIR=`pwd`
TEMP=/home/john/Prog/gradle/wrapper
cd ${TEMP}

gradle wrapper
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




