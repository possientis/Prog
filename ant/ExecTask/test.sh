#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/ExecTask
cd ${HOME}

ant

cd ${DIR}
echo '\ntest completed succesfully\n'




