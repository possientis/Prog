#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/Hello
cd ${HOME}

gradle hW

cd ${DIR}
echo '\ntest completed successfully\n'




