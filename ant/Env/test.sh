#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/Env
cd ${HOME}

ant

cd ${DIR}
echo '\ntest completed succesfully\n'




