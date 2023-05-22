#!/bin/sh

set -e 
DIR=`pwd`
HOME=${HOME}/Prog/ant/ExecTask
cd ${HOME}

ant

cd ${DIR}
echo '\ntest completed successfully\n'




