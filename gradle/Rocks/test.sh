#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/Rocks
cd ${HOME}

gradle gT

cd ${DIR}
echo '\ntest completed successfully\n'




