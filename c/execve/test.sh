#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/execve 
cd ${HOME}

./run.sh

cd ${DIR}
echo '\ntest completed succesfully\n'




