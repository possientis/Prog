#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/JNI
cd ${HOME}

ant
ant clean

cd ${DIR}
echo '\ntest completed successfully\n'




