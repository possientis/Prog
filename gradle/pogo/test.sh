#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/pogo/
cd ${HOME}

gradle printVersion

cd ${DIR}
echo '\ntest completed successfully\n'




