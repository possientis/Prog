#!/bin/sh

# probably need to install the JVM based javascript interpreter rhino

set -e 
DIR=`pwd`
HOME=${HOME}/Prog/ant/Script
cd ${HOME}

ant

cd ${DIR}
echo '\ntest completed successfully\n'




