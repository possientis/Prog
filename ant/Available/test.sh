#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/Available
cd ${HOME}

ant

cd ${DIR}
echo '\ntest completed successfully\n'




