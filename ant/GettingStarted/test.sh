#!/bin/sh

set -e 
DIR=`pwd`
HOME=${HOME}/Prog/ant/GettingStarted
cd ${HOME}

ant
ant clean

cd ${DIR}
echo '\ntest completed successfully\n'




